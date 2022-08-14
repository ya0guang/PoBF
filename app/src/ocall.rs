use std::io::Write;
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};

#[no_mangle]
pub unsafe extern "C" fn u_log_ocall(
    string_ptr: *mut u8,
    string_len: u32,
    string_capacity: u32,
) -> u32 {
    let mut stderr = StandardStream::stderr(ColorChoice::Always);
    stderr.set_color(ColorSpec::new().set_fg(Some(Color::Magenta))).unwrap();

    let s = String::from_raw_parts(string_ptr, string_len as usize, string_capacity as usize);
    writeln!(&mut stderr, "{}", s).unwrap();

    std::mem::forget(s);
    string_capacity
}
