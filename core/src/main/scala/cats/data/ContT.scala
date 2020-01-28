package cats
package data

/**
 * This is a continuation transformer based on the ContT in
 * the Haskell package Control.Monad.Cont
 *
 * This is reasonably straight-forward except that to make
 * a tailRecM implementation we leverage the Defer type class to
 * obtain stack-safety.
 */
sealed abstract class ContT[M[_], A, +B] extends Serializable {
  final def run: (B => M[A]) => M[A] = runAndThen
  protected def runAndThen: AndThen[B => M[A], M[A]]

  final def map[C](fn: B => C)(implicit M: Defer[M]): ContT[M, A, C] = {
    // allocate/pattern match once
    val fnAndThen = AndThen(fn)
    ContT { fn2 =>
      val cb = fnAndThen.andThen(fn2)
      M.defer(run(cb))
    }
  }

  /**
   * c.mapCont(f).run(g) == f(c.run(g))
   */
  final def mapCont(fn: M[A] => M[A]): ContT[M, A, B] =
    // Use later here to avoid forcing run
    ContT.later(runAndThen.andThen(fn))

  /**
   * cont.withCont(f).run(cb) == cont.run(f(cb))
   */
  final def withCont[C](fn: (C => M[A]) => B => M[A]): ContT[M, A, C] =
    // lazy to avoid forcing run
    ContT.later(AndThen(fn).andThen(runAndThen))

  final def flatMap[C](fn: B => ContT[M, A, C])(implicit M: Defer[M]): ContT[M, A, C] = {
    // allocate/pattern match once
    val fnAndThen = AndThen(fn)
    ContT[M, A, C] { fn2 =>
      val contRun: ContT[M, A, C] => M[A] = (_.run(fn2))
      val fn3: B => M[A] = fnAndThen.andThen(contRun)
      M.defer(run(fn3))
    }
  }
}

object ContT extends ContTInstances {

  // Note, we only have two instances of ContT in order to be gentle on the JVM JIT
  // which treats classes with more than two subclasses differently

  private case class FromFn[M[_], A, B](runAndThen: AndThen[B => M[A], M[A]]) extends ContT[M, A, B]

  private case class DeferCont[M[_], A, B](next: () => ContT[M, A, B]) extends ContT[M, A, B] {
    @annotation.tailrec
    private def loop(n: () => ContT[M, A, B]): ContT[M, A, B] =
      n() match {
        case DeferCont(n) => loop(n)
        case notDefer     => notDefer
      }

    lazy val runAndThen: AndThen[B => M[A], M[A]] = loop(next).runAndThen
  }

  /** Lift a pure value into `ContT` */
  def pure[M[_], A, B](b: B): ContT[M, A, B] =
    apply { cb =>
      cb(b)
    }

  /**
   * Similar to [[pure]] but evaluation of the argument is deferred.
   *
   * This is useful for building a computation which calls its continuation as the final step.
   * Instead of writing:
   *
   * {{{
   *   ContT.apply { cb =>
   *     val x = foo()
   *     val y = bar(x)
   *     val z = baz(y)
   *     cb(z)
   *   }
   * }}}
   *
   * you can write:
   *
   * {{{
   *   ContT.defer {
   *     val x = foo()
   *     val y = bar(x)
   *     baz(y)
   *   }
   * }}}
   */
  def defer[M[_], A, B](b: => B): ContT[M, A, B] =
    apply { cb =>
      cb(b)
    }

  /**
   * Build a computation that makes use of a callback, also known as a continuation.
   *
   * Example:
   *
   * {{{
   *   ContT.apply { callback =>
   *     for {
   *       a <- doFirstThing()
   *       b <- doSecondThing(a)
   *       c <- callback(b)
   *       d <- doFourthThing(c)
   *     } yield d
   *   }
   * }}}
   */
  def apply[M[_], A, B](fn: (B => M[A]) => M[A]): ContT[M, A, B] =
    FromFn(AndThen(fn))

  /** Similar to [[apply]] but evaluation of the argument is deferred. */
  def later[M[_], A, B](fn: => (B => M[A]) => M[A]): ContT[M, A, B] =
    DeferCont(() => FromFn(AndThen(fn)))

  def tailRecM[M[_], A, B, C](a: A)(fn: A => ContT[M, C, Either[A, B]])(implicit M: Defer[M]): ContT[M, C, B] =
    ContT[M, C, B] { cb: (B => M[C]) =>
      def go(a: A): M[C] =
        fn(a).run {
          case Left(a)  => M.defer(go(a))
          case Right(b) => M.defer(cb(b))
        }

      go(a)
    }

  implicit def catsDataContTDefer[M[_], B]: Defer[ContT[M, B, *]] =
    new Defer[ContT[M, B, *]] {
      def defer[A](c: => ContT[M, B, A]): ContT[M, B, A] =
        DeferCont(() => c)
    }
}

sealed abstract private[data] class ContTInstances extends ContTInstances1 {
  implicit def catsDataContTMonad[F[_], A](implicit F0: Defer[F]): Monad[ContT[F, A, *]] =
    new ContTMonad[F, A] { implicit val defer: Defer[F] = F0 }
}

sealed abstract private[data] class ContTInstances1 {
  implicit def catsDataContTMonadError[F[_], A, E](implicit defer0: Defer[F], F0: MonadError[F, E]): MonadError[ContT[F, A, *], E] =
    new ContTMonadError[F, A, E] {
      implicit val defer: Defer[F] = defer0
      implicit val F: MonadError[F, E] = F0
    }
}

private trait ContTMonad[M[_], A] extends Monad[ContT[M, A, *]] {
  implicit def defer: Defer[M]

  def pure[B](b: B): ContT[M, A, B] =
    ContT.pure(b)

  override def map[B, C](c: ContT[M, A, B])(fn: B => C): ContT[M, A, C] =
    c.map(fn)

  def flatMap[B, C](c: ContT[M, A, B])(fn: B => ContT[M, A, C]): ContT[M, A, C] =
    c.flatMap(fn)

  def tailRecM[B, C](b: B)(fn: B => ContT[M, A, Either[B, C]]): ContT[M, A, C] =
    ContT.tailRecM(b)(fn)
}

private trait ContTMonadError[F[_], A, E] extends MonadError[ContT[F, A, *], E] with ContTMonad[F, A] {
  implicit def F: MonadError[F, E]

  def raiseError[B](e: E): ContT[F, A, B] =
    ContT(_ => F.raiseError(e))

  def handleErrorWith[B](fa: ContT[F, A, B])(f: E => ContT[F, A, B]): ContT[F, A, B] =
    ContT { continue =>
      F.handleErrorWith(fa.run(continue)){ e =>
        f(e).run(continue)
      }
    }

  override def adaptError[B](fa: ContT[F, A, B])(pf: PartialFunction[E, E]): ContT[F, A, B] =
    ContT { continue =>
      F.adaptError(fa.run(continue))(pf)
    }
}