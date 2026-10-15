//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

const LABEL: &str = "NaN";
const BYTES: &[u8] = b"static";
pub fn static_label() -> &'static str {
    LABEL
}
pub fn static_bytes() -> &'static [u8] {
    BYTES
}
pub fn accept_static(_label: &'static str, value: u32) -> u32 {
    value
}

pub fn update_static(value: &'static mut u32) -> u32 {
    *value += 1;
    *value
}

pub struct Buffer {
    pub bytes: [u8; 3],
}
impl Buffer {
    pub fn label(&mut self) -> &str {
        static_label()
    }
    pub fn choose(&mut self, use_static: bool) -> &[u8] {
        if use_static {
            static_bytes()
        } else {
            &self.bytes
        }
    }
    pub fn unchanged(&self) -> &[u8] {
        &self.bytes
    }
}

pub trait Label {
    fn required(&self) -> &'static str;
    fn provided(&self) -> &'static str {
        LABEL
    }
}
impl Label for u32 {
    fn required(&self) -> &'static str {
        LABEL
    }
}
pub struct Holder<'a>(pub &'a u8);
impl Label for Holder<'_> {
    fn required(&self) -> &'static str {
        LABEL
    }
}
pub fn required<'a, T: Label>(owner: &'a mut Buffer, value: &T) -> &'a str {
    let _ = owner;
    value.required()
}
pub fn provided<'a, T: Label>(owner: &'a mut Buffer, value: &T) -> &'a str {
    let _ = owner;
    value.provided()
}

pub trait BorrowedLabel<T> {
    fn label<'b>(&self, value: &'b T) -> &'static str;
}
impl<'a> BorrowedLabel<u8> for Holder<'a> {
    fn label<'b>(&self, _value: &'b u8) -> &'static str {
        LABEL
    }
}
pub fn borrowed<'a>(owner: &'a mut Buffer, holder: &Holder<'_>, value: &u8) -> &'a str {
    let _ = owner;
    holder.label(value)
}

#[verify::test]
pub fn regression() {
    let mut owner = Buffer { bytes: [7, 8, 9] };
    let _ = owner.label();
    assert!(owner.choose(true).len() == 6);
    assert!(owner.choose(false)[0] == 7);
    assert!(owner.unchanged()[1] == 8);
    assert!(accept_static(LABEL, 17) == 17);
    let _ = required(&mut owner, &42u32);
    let _ = provided(&mut owner, &42u32);
    let byte = 1u8;
    let holder = Holder(&byte);
    let _ = required(&mut owner, &holder);
    let _ = provided(&mut owner, &holder);
    let _ = borrowed(&mut owner, &holder, &byte);
}

#[cfg(test)]
#[test]
fn rust_regression() {
    regression();
    assert_eq!(update_static(Box::leak(Box::new(7))), 8);
    let mut owner = Buffer { bytes: [7, 8, 9] };
    assert_eq!(owner.label(), "NaN");
    assert_eq!(required(&mut owner, &42u32), "NaN");
    assert_eq!(provided(&mut owner, &42u32), "NaN");
    let byte = 1;
    let holder = Holder(&byte);
    assert_eq!(borrowed(&mut owner, &holder, &byte), "NaN");
}
