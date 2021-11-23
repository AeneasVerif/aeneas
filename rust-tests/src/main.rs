/// The following code generates the limits for the scalar types

fn main() {
    let ints_lower = [
        "isize", "i8", "i16", "i32", "i64", "i128", "usize", "u8", "u16", "u32", "u64", "u128",
    ];

    let ints_upper = [
        "Isize", "I8", "I16", "I32", "I64", "I128", "Usize", "U8", "U16", "U32", "U64", "U128",
    ];

    let mut ints_pairs = vec![];
    for i in 0..ints_lower.len() {
        ints_pairs.push((&ints_lower[i], &ints_upper[i]));
    }

    // Generate the code to print the scalar ranges
    for s in &ints_lower {
        println!(
            "println!(\"let {}_min = Z.of_string \\\"{{}}\\\"\", {}::MIN);",
            s, s
        );
        println!(
            "println!(\"let {}_max = Z.of_string \\\"{{}}\\\"\", {}::MAX);",
            s, s
        );
    }
    println!("\n");

    // Generate the OCaml definitions for the ranges - this code is
    // generated (comes from the above)
    println!("let isize_min = Z.of_string \"{}\"", isize::MIN);
    println!("let isize_max = Z.of_string \"{}\"", isize::MAX);
    println!("let i8_min = Z.of_string \"{}\"", i8::MIN);
    println!("let i8_max = Z.of_string \"{}\"", i8::MAX);
    println!("let i16_min = Z.of_string \"{}\"", i16::MIN);
    println!("let i16_max = Z.of_string \"{}\"", i16::MAX);
    println!("let i32_min = Z.of_string \"{}\"", i32::MIN);
    println!("let i32_max = Z.of_string \"{}\"", i32::MAX);
    println!("let i64_min = Z.of_string \"{}\"", i64::MIN);
    println!("let i64_max = Z.of_string \"{}\"", i64::MAX);
    println!("let i128_min = Z.of_string \"{}\"", i128::MIN);
    println!("let i128_max = Z.of_string \"{}\"", i128::MAX);
    println!("let usize_min = Z.of_string \"{}\"", usize::MIN);
    println!("let usize_max = Z.of_string \"{}\"", usize::MAX);
    println!("let u8_min = Z.of_string \"{}\"", u8::MIN);
    println!("let u8_max = Z.of_string \"{}\"", u8::MAX);
    println!("let u16_min = Z.of_string \"{}\"", u16::MIN);
    println!("let u16_max = Z.of_string \"{}\"", u16::MAX);
    println!("let u32_min = Z.of_string \"{}\"", u32::MIN);
    println!("let u32_max = Z.of_string \"{}\"", u32::MAX);
    println!("let u64_min = Z.of_string \"{}\"", u64::MIN);
    println!("let u64_max = Z.of_string \"{}\"", u64::MAX);
    println!("let u128_min = Z.of_string \"{}\"", u128::MIN);
    println!("let u128_max = Z.of_string \"{}\"", u128::MAX);
    println!("\n");

    // Generate the check_int_in_range body
    for (lo, up) in &ints_pairs {
        println!("| {} -> Z.leq {}_min i && Z.leq i {}_max", up, lo, lo);
    }
    println!("\n");

    // Generate the scalar_value_get_value_range body
    for s in &ints_upper {
        println!("| {} i -> i", s);
    }
    println!("\n");
}
