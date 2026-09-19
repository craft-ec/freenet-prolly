//! Computes the frozen root vectors on wasm32 so `check-wasm.sh` can compare
//! them with `tests/vectors.txt`: boundaries must not depend on the target.

#[path = "../../tests/common/dataset.rs"]
mod common;

use freenet_prolly::build::build;
use freenet_prolly::node::Value;

/// Root cid of `dataset(1, n)`, written to a static buffer; returns its address.
#[no_mangle]
pub extern "C" fn root(n: u32) -> *const u8 {
    static mut OUT: [u8; 32] = [0; 32];
    let e = common::dataset(1, n as usize);
    let r = build(
        e.iter().map(|(k, v)| (k.as_slice(), Value::Inline(v))),
        |_, _| {},
    )
    .unwrap();
    unsafe {
        OUT = r;
        &raw const OUT as *const u8
    }
}
