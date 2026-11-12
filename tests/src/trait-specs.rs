//@ [!lean] skip
//@ [lean] subdir=TraitSpecs
#![feature(register_tool)]
#![register_tool(verify)]
//! Generic code whose specs assume specs of the instance's methods (see `TraitSpecs/Properties.lean`).

/// A default method calling a fallible method.
pub trait Priced {
    fn price(&self) -> u32;
    fn with_tax(&self) -> u32 {
        let p = self.price();
        p + p / 5
    }
}

pub struct Item {
    pub unit: u32,
    pub qty: u32,
}

impl Priced for Item {
    fn price(&self) -> u32 {
        self.unit * self.qty
    }
}

/// A generic function; the instance's method branches.
pub trait Keyed {
    fn key(&self) -> u32;
}

pub fn max_key<T: Keyed>(a: &T, b: &T) -> u32 {
    let ka = a.key();
    let kb = b.key();
    if ka >= kb {
        ka
    } else {
        kb
    }
}

pub struct Employee {
    pub salary: u32,
    pub bonus: u32,
}

impl Keyed for Employee {
    fn key(&self) -> u32 {
        if self.bonus > self.salary {
            self.bonus
        } else {
            self.salary
        }
    }
}

pub fn max_employee_key(a: &Employee, b: &Employee) -> u32 {
    max_key(a, b)
}

/// A method with an extra argument.
pub trait Fee {
    fn fee(&self, amount: u32) -> u32;
    fn total(&self, amount: u32) -> u32 {
        amount + self.fee(amount)
    }
}

pub struct PercentFee {
    pub percent: u32,
}

impl Fee for PercentFee {
    fn fee(&self, amount: u32) -> u32 {
        amount / 100 * self.percent
    }
}

pub fn percent_total(f: &PercentFee, amount: u32) -> u32 {
    f.total(amount)
}

/// A method taking `&mut self`.
pub trait Account {
    fn deposit(&mut self, amount: u32);
    fn deposit_two(&mut self, a: u32, b: u32) {
        self.deposit(a);
        self.deposit(b);
    }
}

pub struct Wallet {
    pub cents: u32,
}

impl Account for Wallet {
    fn deposit(&mut self, amount: u32) {
        self.cents += amount;
    }
}

pub fn wallet_deposit_two(w: &mut Wallet, a: u32, b: u32) {
    w.deposit_two(a, b)
}

/// Two methods returning constants.
pub trait Bounded {
    fn lo(&self) -> u32;
    fn hi(&self) -> u32;
    fn clamp(&self, x: u32) -> u32 {
        let lo = self.lo();
        let hi = self.hi();
        if x < lo {
            lo
        } else if x > hi {
            hi
        } else {
            x
        }
    }
}

pub struct Percent;

impl Bounded for Percent {
    fn lo(&self) -> u32 {
        0
    }
    fn hi(&self) -> u32 {
        100
    }
}

pub fn clamp_percent(x: u32) -> u32 {
    Percent.clamp(x)
}

/// A generic impl.
pub struct Pair<T> {
    pub first: T,
    pub second: T,
}

impl<T: Priced> Priced for Pair<T> {
    fn price(&self) -> u32 {
        self.first.price() + self.second.price()
    }
}

pub fn pair_with_tax(p: &Pair<Item>) -> u32 {
    p.with_tax()
}

#[verify::test]
pub fn test_trait_specs() {
    let a = Employee {
        salary: 10,
        bonus: 20,
    };
    let b = Employee {
        salary: 15,
        bonus: 0,
    };
    assert!(max_employee_key(&a, &b) == 20);
    assert!(percent_total(&PercentFee { percent: 2 }, 500) == 510);
    let mut w = Wallet { cents: 1 };
    wallet_deposit_two(&mut w, 2, 3);
    assert!(w.cents == 6);
    assert!(clamp_percent(150) == 100);
    assert!(clamp_percent(42) == 42);
    let p = Pair {
        first: Item { unit: 10, qty: 1 },
        second: Item { unit: 5, qty: 4 },
    };
    assert!(pair_with_tax(&p) == 36);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trait_specs() {
        test_trait_specs()
    }
}
