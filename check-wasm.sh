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
const want = fs.readFileSync('tests/vectors.txt', 'utf8').split('\n')
  .filter(l => l.startsWith('root ')).map(l => l.split(' '));
if (want.length === 0) { console.error('no root vectors found'); process.exit(1); }
WebAssembly.instantiate(wasm).then(({ instance }) => {
  let bad = 0;
  for (const [, n, hex] of want) {
    const p = instance.exports.root(Number(n));
    const got = Buffer.from(new Uint8Array(instance.exports.memory.buffer, p, 32)).toString('hex');
    if (got !== hex) { bad++; console.error(`root ${n}: wasm32 ${got} != native ${hex}`); }
  }
  console.log(`wasm32 roots: ${want.length - bad}/${want.length} match native`);
  process.exit(bad ? 1 : 0);
});
JS
