/*
 * Copyright 2014 - 2016 SlamData Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package invertible

import scalaz._, Scalaz._
import Leibniz.===

trait Syntax[P[_]] extends IsoFunctor[P] with ProductFunctor[P] with Alternative[P] {
  /** A value that does not appear in the text at all. */
  def pure[A](a: A): P[A]

  /** Pull(push) a single char from(to) the text. */
  def token: P[Char]

  /** Pull(push) a fixed number of characters at once from(to) the text. */
  def tokenStr(length: Int): P[String]

  /** Record the position before and after parsing some value. The position
    * is ignored when pretty-printing.
    */
  def pos[A](p: P[A]): P[(A, Position)]

  /** Wrap a parser with a label used in error reporting. */
  def label[A](p: P[A], expected: => String): P[A]
}
object Syntax {
  import Iso._

  // TODO: make most of these syntax on `P[_]: Syntax`

  def many[A, P[_]](p: P[A])(implicit S: Syntax[P]): P[List[A]] =
    (S.pure(()) ∘ Iso.nil[A]) | many1(p)

  def many1[A, P[_]](p: P[A])(implicit S: Syntax[P]): P[List[A]] =
    (p * many(p)) ∘ Iso.cons

  def sepBy1[A, P[_]](p: P[A], sep: P[Unit])(implicit S: Syntax[P]): P[List[A]] =
    p * many(sep *> p) ^ cons

  def text[A, P[_]](s: String)(implicit S: Syntax[P]): P[Unit] =
    if (s == "") S.pure(())
    else
      S.label(S.tokenStr(s.length) ∘ element(s).inverse, "\"" + s + "\"")

  def digit[P[_]](implicit S: Syntax[P]): P[Char] =
    S.label(S.token ∘ subset[Char](_.isDigit), "digit")

  def letter[P[_]](implicit S: Syntax[P]): P[Char] =
    S.label(S.token ∘ subset[Char](_.isLetter), "letter")

  def int[P[_]](implicit S: Syntax[P]): P[BigInt] =
    many(digit) ^ chars ^ Iso.int

  def *>[A, P[_]](f: P[Unit], g: P[A])(implicit S: Syntax[P]): P[A] =
    (f * g) ∘ (unit[A] >>> commute).inverse

  def <*[A, P[_]](f: P[A], g: P[Unit])(implicit S: Syntax[P]): P[A] =
    (f * g) ∘ unit.inverse

  def between[A, P[_]](f: P[Unit], g: P[Unit])(h: P[A])(implicit S: Syntax[P]): P[A] =
    f *> h <* g

  def optional[A, P[_]](f: P[A])(implicit S: Syntax[P]): P[Option[A]] =
    (f ∘ some[A]) | (text("") ∘ none[A])

  /**
    arg: a parser/printer for each term, which will handle higher-precedence ops.
    op: a parser/printer for _all_ infix operators.
    f: an iso which applies only to operators (B) with this precedence.
    */
  def chainl1[A, B, P[_]](arg: P[A], op: P[B], f: Iso[(A, (B, A)), A])(implicit S: Syntax[P]): P[A] =
    (arg * many (op * arg)) ∘ foldl(f)

  /** Accept 0 or more spaces, emit none. */
  def skipSpace[P[_]](implicit S: Syntax[P]): P[Unit] =
    many(text(" ")) ∘ ignore(List[Unit]())

  /** Accept 0 or more spaces, emit one. */
  def optSpace[P[_]](implicit S: Syntax[P]): P[Unit] =
    many(text(" ")) ∘ ignore(List(()))

  /** Accept 1 or more spaces, emit one. */
  def sepSpace[P[_]](implicit S: Syntax[P]): P[Unit] =
    text(" ") <* skipSpace

  /*
    Compare with the operators from Haskell's invertible-syntax:
    *> (9 assumed)         *> (8)
    <* (9 assumed)         <* (5)  // That's not good (TODO: :, +, -, *, /, %) (*< ???)
    infixr 6 <*>           * (8) (TODO: <*> (5))
    infix  5 <$>           map/∘ (with the operands reversed) (0/9) (TODO: ^(2), &(3), =(4), !(4))
    infixl 4 <+>           <+> (5) (TODO: |+| (1))
    infixl 3 <|>           | (1)
    (See http://scala-lang.org/files/archive/spec/2.11/06-expressions.html#infix-operations)
   */

  implicit class SyntaxOps[A, P[_]](f: P[A])(implicit S: Syntax[P]) {
    def map[B](iso: Iso[A, B]): P[B] = S.map(f, iso)
    /** Alias for `map`. */
    def ∘[B](iso: Iso[A, B]): P[B] = S.map(f, iso)
    /** Alias for `map` with low precedence. */
    def ^[B](iso: Iso[A, B]): P[B] = S.map(f, iso)

    def *[B](g: => P[B]) = S.and(f, g)
    /** Alias for `*` with medium precedence. */
    def <*>[B](g: => P[B]) = S.and(f, g)

    def |(g: => P[A]) = S.or(f, g)

    def <*(g: P[Unit]) = Syntax.<*(f, g)
    /** Alias for `<*` with highest precedence. */
    def *<(g: P[Unit]) = Syntax.<*(f, g)

    def *>[B](g: P[B])(implicit ev: A === Unit) = Syntax.*>(ev.subst(f), g)

    def <+>[B](g: P[B]): P[A \/ B] = (f ∘ left[A, B]) | (g ∘ right[A, B])
    // TODO: |+|
  }

  /** A parser is simply a pure function from an input sequence to a tuple of:
   * - an optional failure, which represents the most advanced failure yet seen, and
   * - a list of possible results, each paired with the remaining input.
   */
  type Parser[A] = Source => (Option[ParseFailure], List[(A, Source)])

  val ParserSyntax = new Syntax[Parser] {
    def map[A, B](p: Parser[A], iso: Iso[A, B]) = { r =>
      val (e, ps1) = p(r)
      (e,
        ps1.flatMap { case (a, r1) =>
          iso.app(a).fold[List[(B, Source)]](Nil)((_, r1) :: Nil)
        })
    }

    def and[A, B](fa: Parser[A], fb: => Parser[B]) = { r =>
      val (e1, ps1) = fa(r)
      val (e2s: List[Option[ParseFailure]], ps2s: List[List[((A, B), Source)]]) =
        ps1.map { case (a, r1) =>
          val (e, ps2) = fb(r1)
          (e, ps2.map { case (b, r2) => ((a, b), r2) })
        }.unzip
      ((None :: e1 :: e2s).reduce(_ |+| _),
        ps2s.flatten)
    }

    def or[A](f1: Parser[A], f2: => Parser[A]) = { r =>
      val (e1, ps1) = f1(r)
      val (e2, ps2) = f2(r)
      (e1 |+| e2, ps1 ++ ps2)
    }

    def pure[A](a: A) =
      r => (None, List((a, r)))

    def token: Parser[Char] = r =>
      r.first.cata(
        c => (None, List((c, r.rest))),
        (Some(ParseFailure(r, "any char")), Nil))

    def tokenStr(length: Int): Parser[String] = { r =>
      r.prefix(length).cata(
        s => (None, List((s, r.drop(length)))),
        (Some(ParseFailure(r, "any " + length + " chars")), Nil))
    }

    def pos[A](p: Parser[A]): Parser[(A, Position)] = { r =>
      val before = r.pos
      p(r).map(_.map {
        case (a, r1) => ((a, before |+| r1.pos), r1)
      })
    }

    def label[A](p: Parser[A], expected: => String) = { r =>
      val (_, ps) = p(r)
      (if (ps.isEmpty) Some(ParseFailure(r, expected)) else None,
        ps)
    }
  }

  def parser[A](syntax: Syntax[Parser] => Parser[A]): String => (ParseFailure \/ A) = {
    val p = syntax(Syntax.ParserSyntax)

    { s =>
      val r = new Source(s, 0)
      val (err, ps) = p(r)
      val as = ps.collect { case (a, rem) if rem.atEnd => a }
      (err, as) match {
        case (_, a :: Nil)            => \/-(a)
        case (_, as) if as.length > 1 => sys.error("TODO: ambiguous parse")
        case (Some(err), Nil)         => -\/(err)
        case (None, Nil)              => sys.error("TODO: no parse and no error")
      }
    }
  }


  type Printer[A] = A => Option[Cord]

  val PrinterSyntax = new Syntax[Printer] {
    def map[A, B](p: Printer[A], iso: Iso[A, B]) =
      b => iso.unapp(b).flatMap(p)

    def and[A, B](fa: Printer[A], fb: => Printer[B]) =
      { case (a, b) => (fa(a) |@| fb(b))(_ ++ _) }

    def or[A](f1: Printer[A], f2: => Printer[A]) =
      a => f1(a).orElse(f2(a))

    def pure[A](a: A) = x => if (x == a) Some("") else None

    def token = c => Some(c.toString)

    def tokenStr(length: Int) = s => Some(s)

    def pos[A](p: Printer[A]) = { case (a, _) => p(a) }

    def label[A](p: Printer[A], expected: => String) = p
  }

  def printer[A](syntax: Syntax[Printer] => Printer[A]): A => Option[Cord] =
    syntax(Syntax.PrinterSyntax)
}
