#[no_mangle]
pub unsafe extern "C" fn u_log_ocall(
    string_ptr: *mut u8,
    string_len: u32,
    string_capacity: u32,
) -> u32 {
    let s = String::from_raw_parts(string_ptr, string_len as usize, string_capacity as usize);
    println!("{}", s);
    std::mem::forget(s);
    string_capacity
}
