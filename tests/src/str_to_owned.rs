//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

const HELLO: &str = "hello";

#[verify::test]
pub fn test_str_to_owned() {
    let s: &str = HELLO;
    let _owned: String = s.to_owned();
}
