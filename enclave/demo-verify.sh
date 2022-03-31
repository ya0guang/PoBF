 #!/bin/bash

export PATH="../verifier:$PATH"
cargo pobf-verify --allowed-unsafe lib.rs ocall.rs --log-level INFO -- --features violation
