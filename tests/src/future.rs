//@ [!lean] skip
//@ [lean] subdir=Future
//@ charon-args=--include=core::pin::Pin
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of `Future`, `Poll`, `Context`, `Waker` and `Pin`.
//!
//! The futures are written by hand. `AddOne` is what the state machine of
//! `async fn add_one<F: Future<Output = u32>>(f: F) -> u32 { f.await + 1 }` looks like.
//!
//! The first two tests are the examples of the documentation of `Poll::is_ready` and
//! `Poll::is_pending` (<https://doc.rust-lang.org/std/task/enum.Poll.html>); `test_noop_waker`
//! adapts the one of `Waker::noop` (<https://doc.rust-lang.org/std/task/struct.Waker.html#method.noop>),
//! which uses an `async` block and `Box::pin`.

use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll, Waker};

pub fn is_ready(poll: Poll<usize>) -> bool {
    poll.is_ready()
}

pub fn is_pending(poll: Poll<usize>) -> bool {
    poll.is_pending()
}

#[verify::test]
pub fn test_is_ready() {
    assert!(is_ready(Poll::Ready(42)));
    assert!(!is_ready(Poll::Pending));
}

#[verify::test]
pub fn test_is_pending() {
    assert!(!is_pending(Poll::Ready(42)));
    assert!(is_pending(Poll::Pending));
}

/// A future which is ready the first time it is polled.
pub struct Ready<T>(Option<T>);

impl<T> Ready<T> {
    pub fn new(value: T) -> Self {
        Ready(Some(value))
    }
}

impl<T: Unpin> Future for Ready<T> {
    type Output = T;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<T> {
        // Panics if the future is polled again after it completed
        Poll::Ready(self.0.take().unwrap())
    }
}

/// A future which is pending `n` times, then ready with the value `42`.
pub struct Countdown(pub u32);

impl Future for Countdown {
    type Output = u32;

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u32> {
        let this = self.get_mut();
        if this.0 == 0 {
            Poll::Ready(42)
        } else {
            this.0 -= 1;
            Poll::Pending
        }
    }
}

/// A future which asks to be polled again, and is pending the first time it is polled.
pub struct YieldNow(pub bool);

impl Future for YieldNow {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.0 {
            Poll::Ready(())
        } else {
            self.0 = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

/// Polls the future once, with a context whose waker does nothing.
pub fn poll_once<F: Future + Unpin>(future: &mut F) -> Poll<F::Output> {
    let mut cx = Context::from_waker(Waker::noop());
    Pin::new(future).poll(&mut cx)
}

/// The state machine of `async { inner.await + 1 }`: it forwards the polls to `inner`.
pub struct AddOne<F: Future<Output = u32>> {
    pub inner: F,
}

impl<F: Future<Output = u32>> Future for AddOne<F> {
    type Output = u32;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<u32> {
        // SAFETY: `inner` is never moved out of `self`
        let this = unsafe { self.get_unchecked_mut() };
        let inner = unsafe { Pin::new_unchecked(&mut this.inner) };
        match inner.poll(cx) {
            Poll::Ready(value) => Poll::Ready(value + 1),
            Poll::Pending => Poll::Pending,
        }
    }
}

/// The loop of a single-task executor: poll until the future is ready.
pub fn block_on<F: Future + Unpin>(future: &mut F) -> F::Output {
    let mut cx = Context::from_waker(Waker::noop());
    loop {
        if let Poll::Ready(value) = Pin::new(&mut *future).poll(&mut cx) {
            return value;
        }
    }
}

#[verify::test]
pub fn test_noop_waker() {
    let mut cx = Context::from_waker(Waker::noop());
    let mut future = Ready::new(10);
    assert!(matches!(
        Pin::new(&mut future).poll(&mut cx),
        Poll::Ready(10)
    ));
}

#[verify::test]
pub fn test_countdown() {
    let mut future = Countdown(2);
    assert!(matches!(poll_once(&mut future), Poll::Pending));
    assert!(matches!(poll_once(&mut future), Poll::Pending));
    assert!(matches!(poll_once(&mut future), Poll::Ready(42)));
}

#[verify::test]
pub fn test_yield_now() {
    let mut future = YieldNow(false);
    assert!(matches!(poll_once(&mut future), Poll::Pending));
    assert!(matches!(poll_once(&mut future), Poll::Ready(())));
}

#[verify::test]
pub fn test_add_one() {
    let mut future = AddOne {
        inner: Countdown(1),
    };
    assert!(matches!(poll_once(&mut future), Poll::Pending));
    assert!(matches!(poll_once(&mut future), Poll::Ready(43)));
}

#[verify::test]
pub fn test_block_on() {
    block_on(&mut YieldNow(false));
    assert_eq!(block_on(&mut Countdown(3)), 42);
    assert_eq!(
        block_on(&mut AddOne {
            inner: Countdown(3)
        }),
        43
    );
}

#[cfg(test)]
mod tests {
    #[test]
    fn future() {
        super::test_is_ready();
        super::test_is_pending();
        super::test_noop_waker();
        super::test_countdown();
        super::test_yield_now();
        super::test_add_one();
        super::test_block_on();
    }
}
