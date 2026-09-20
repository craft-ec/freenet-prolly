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
  // Parity: the code and the repair must be identical on this target, or
  // "anyone can repair without a key" is a claim about one machine.
  const parity = lines.filter(l => l.startsWith('parity ')).map(l => l.split(' '));
  const prepair = lines.filter(l => l.startsWith('prepair ')).map(l => l.split(' '));
  if (parity.length === 0 || prepair.length === 0) {
    console.error('no parity vectors found'); process.exit(1);
  }
  for (const [, k, plen, p0, p1, p2] of parity) {
    const at = instance.exports.parity_ids(Number(k));
    const got = [0, 1, 2].map(i =>
      Buffer.from(new Uint8Array(instance.exports.memory.buffer, at + i * 32, 32)).toString('hex'));
    if (got[0] !== p0 || got[1] !== p1 || got[2] !== p2) {
      bad++; console.error(`parity ${k}: wasm32 ${got.join(' ')} != native ${p0} ${p1} ${p2}`);
    }
    const gotLen = instance.exports.parity_len(Number(k));
    if (gotLen !== Number(plen)) {
      bad++; console.error(`parity ${k}: wasm32 trimmed length ${gotLen} != native ${plen}`);
    }
  }
  for (const [, k, hex] of prepair) {
    const got = read32(instance.exports.parity_repair_digest(Number(k)));
    if (got !== hex) { bad++; console.error(`prepair ${k}: wasm32 ${got} != native ${hex}`); }
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
  // The empty final page of a listing, at the WIRE door — the page a light
  // client sees when it finishes reading a feed.
  for (const n of [1000, 5000]) {
    if (instance.exports.empty_final_page_ok(n) !== 1) {
      bad++;
      console.error(`empty final page (${n} entries): not verified on wasm32`);
    }
  }
  // Every lane prints what it COVERED, not only that it found nothing wrong:
  // "0 bad" over a lane that never ran reads exactly like a passing one.
  console.log(`wasm32: ${want.length} roots, ${proofs.length} key proofs, ${rproofs.length} range proofs, ${parity.length} parity groups and ${prepair.length} repair sweeps match native and verify (${bad} bad)`);
  if (parity.length === 0 || prepair.length === 0) {
    console.error('parity lane covered nothing'); process.exit(1);
  }
  process.exit(bad ? 1 : 0);
});
JS
