//@ [fstar] aeneas-args=-decreases-clauses -split-files
//@ [coq] aeneas-args=-use-fuel
//@ [coq,fstar] subdir=misc
#![feature(register_tool)]
#![register_tool(charon)]
#![register_tool(aeneas)]

#[charon::rename("BoolTest")]
pub trait BoolTrait {
    // Required method
    #[charon::rename("getTest")]
    fn get_bool(&self) -> bool;

    // Provided method
    #[charon::rename("retTest")]
    fn ret_true(&self) -> bool {
        true
    }
}

#[charon::rename("BoolImpl")]
impl BoolTrait for bool {
    fn get_bool(&self) -> bool {
        *self
    }
}

#[charon::rename("BoolFn")]
pub fn test_bool_trait<T>(x: bool) -> bool {
    x.get_bool() && x.ret_true()
}

#[charon::rename("TypeTest")]
type Test = i32;

#[charon::rename("VariantsTest")]
enum SimpleEnum {
    #[charon::rename("Variant1")]
    FirstVariant,
    SecondVariant,
    ThirdVariant,
}

#[charon::rename("StructTest")]
struct Foo {
    #[charon::rename("FieldTest")]
    field1: u32,
}

#[charon::rename("Const_Test")]
const C: u32 = 100 + 10 + 1;

#[aeneas::rename("Const_Aeneas11")]
const CA: u32 = 10 + 1;

#[charon::rename("Factfn")]
fn factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        return n * factorial(n - 1);
    }
}

#[charon::rename("No_borrows_sum")]
pub fn sum(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < max {
        s += i;
        i += 1;
    }

    s *= 2;
    s
}
