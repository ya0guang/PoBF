# User Application: A Demo
This crate demonstrates how private computation is done.

Recall that we have three major components for PoBF:
* The enclave code (written in Rust) that provides the PoBF core functionalities.
* The lib.rs for main entry exportation.
* The C wrapper for the main entry that can be invoked by user applications.

Therefore, by writing application (either in C / C++ / Rust), we can invoke the interface of PoBF easily. For example, in this crate, we wrote a `main.rs` file for reading encrypted data and sealing key stream, and then the code will pass all the data to the `private_computing_entry` interface, which later invokes the `pobf_private_computing` function in enclave.
