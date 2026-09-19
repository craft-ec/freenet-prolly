#!/bin/sh
# Build the library for wasm32 and check it produces the same frozen roots as native.
set -eu
cd "$(dirname "$0")"
command -v node >/dev/null || { echo "check-wasm: node is required" >&2; exit 1; }
rustup target list --installed | grep -qx wasm32-unknown-unknown ||
  { echo "check-wasm: rust target wasm32-unknown-unknown is required" >&2; exit 1; }
cargo build --quiet --release --target wasm32-unknown-unknown --manifest-path wasm-check/Cargo.toml
node - <<'JS'
const fs = require('fs');
const wasm = fs.readFileSync('wasm-check/target/wasm32-unknown-unknown/release/wasm_check.wasm');
const lines = fs.readFileSync('tests/vectors.txt', 'utf8').split('\n');
const want = lines.filter(l => l.startsWith('root ')).map(l => l.split(' '));
const proofs = lines.filter(l => l.startsWith('proof ')).map(l => l.split(' '));
if (want.length === 0) { console.error('no root vectors found'); process.exit(1); }
if (proofs.length === 0) { console.error('no proof vectors found'); process.exit(1); }
WebAssembly.instantiate(wasm).then(({ instance }) => {
  let bad = 0;
  const read32 = p => Buffer.from(new Uint8Array(instance.exports.memory.buffer, p, 32)).toString('hex');
  for (const [, n, hex] of want) {
    const got = read32(instance.exports.root(Number(n)));
    if (got !== hex) { bad++; console.error(`root ${n}: wasm32 ${got} != native ${hex}`); }
  }
  // A proof must be the same BYTES here and verify HERE. Byte equality alone
  // would pass for a proof this target cannot check.
  for (const [, n, , nodes, bytes, hex] of proofs) {
    const got = read32(instance.exports.proof_hash(Number(n)));
    if (got !== hex) { bad++; console.error(`proof ${n}: wasm32 ${got} != native ${hex}`); }
    const shape = instance.exports.proof_shape(Number(n));
    const gotNodes = Number(shape >> 32n), gotBytes = Number(shape & 0xffffffffn);
    if (gotNodes !== Number(nodes) || gotBytes !== Number(bytes)) {
      bad++;
      console.error(`proof ${n}: wasm32 ${gotNodes} nodes/${gotBytes} B != native ${nodes}/${bytes}`);
    }
    if (instance.exports.proof_verify(Number(n)) !== 1) {
      bad++; console.error(`proof ${n}: does not verify on wasm32`);
    }
  }
  // Range proofs: a LISTING must be the same bytes here and verify here.
  const rproofs = lines.filter(l => l.startsWith('rproof ')).map(l => l.split(' '));
  if (rproofs.length === 0) { console.error('no range-proof vectors found'); process.exit(1); }
  for (const [, n, nodes, bytes, hex] of rproofs) {
    const got = read32(instance.exports.range_proof_hash(Number(n)));
    if (got !== hex) { bad++; console.error(`rproof ${n}: wasm32 ${got} != native ${hex}`); }
    const shape = instance.exports.range_proof_shape(Number(n));
    const gotNodes = Number(shape >> 32n), gotBytes = Number(shape & 0xffffffffn);
    if (gotNodes !== Number(nodes) || gotBytes !== Number(bytes)) {
      bad++;
      console.error(`rproof ${n}: wasm32 ${gotNodes} nodes/${gotBytes} B != native ${nodes}/${bytes}`);
    }
    if (instance.exports.range_proof_verify(Number(n)) !== 1) {
      bad++; console.error(`rproof ${n}: does not verify on wasm32`);
    }
  }
  console.log(`wasm32: ${want.length} roots, ${proofs.length} key proofs and ${rproofs.length} range proofs match native and verify (${bad} bad)`);
  process.exit(bad ? 1 : 0);
});
JS
