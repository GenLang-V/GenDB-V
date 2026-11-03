#!/usr/bin/env node
// Copies the mascot picture into docs/assets/: node docs/build/hero.mjs --from DIR
// DIR holds hero-s.svg. Each embedded PNG is stored again with zlib level 9 (same scanlines, so the same pixels).
// The file must have a viewBox and a <title>, no reference outside itself, and the canvas size that js/pages/home.js
// gives its picture (width, height). The home page shows it (HERO in js/pages/home.js).
import fs from "node:fs";
import path from "node:path";
import zlib from "node:zlib";
import { fileURLToPath } from "node:url";

const NAMES = ["hero-s"];
const site = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const i = process.argv.indexOf("--from");
if (i < 0 || !process.argv[i + 1]) {
  console.error("usage: node docs/build/hero.mjs --from DIR");
  process.exit(2);
}
const from = path.resolve(process.argv[i + 1]);

const CRC = new Uint32Array(256).map((_, n) => {
  let c = n;
  for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
  return c >>> 0;
});
function crc32(buf) {
  let c = 0xffffffff;
  for (const b of buf) c = CRC[(c ^ b) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
function chunk(type, data) {
  const head = Buffer.alloc(8);
  head.writeUInt32BE(data.length, 0);
  head.write(type, 4, "latin1");
  const crc = Buffer.alloc(4);
  crc.writeUInt32BE(crc32(Buffer.concat([head.subarray(4), data])), 0);
  return Buffer.concat([head, data, crc]);
}

/** The PNG with all its IDAT data in one chunk, deflated at level 9; other chunks unchanged. */
function recompress(png) {
  const sig = png.subarray(0, 8);
  const parts = [sig], idat = [];
  let at = 8, placed = false;
  while (at < png.length) {
    const len = png.readUInt32BE(at), type = png.toString("latin1", at + 4, at + 8);
    const whole = png.subarray(at, at + 12 + len);
    if (type === "IDAT") {
      idat.push(png.subarray(at + 8, at + 8 + len));
      if (!placed) { parts.push(null); placed = true; }
    } else parts.push(whole);
    at += 12 + len;
  }
  const raw = zlib.inflateSync(Buffer.concat(idat));
  const packed = chunk("IDAT", zlib.deflateSync(raw, { level: 9 }));
  if (!zlib.inflateSync(packed.subarray(8, packed.length - 4)).equals(raw)) throw new Error("recompressed IDAT differs");
  return Buffer.concat(parts.map((p) => p || packed));
}

const home = fs.readFileSync(path.join(site, "js/pages/home.js"), "utf8");
const size = /src: HERO, width: "(\d+)", height: "(\d+)"/.exec(home);
if (!size) throw new Error("js/pages/home.js: no width and height for the picture");
for (const name of NAMES) {
  const src = path.join(from, `${name}.svg`);
  let svg = fs.readFileSync(src, "utf8");
  const box = /<svg[^>]*viewBox="0 0 (\d+) (\d+)"/.exec(svg);
  if (!box) throw new Error(`${name}: no viewBox`);
  if (box[1] !== size[1] || box[2] !== size[2]) throw new Error(`${name}: canvas ${box[1]}x${box[2]}, js/pages/home.js says ${size[1]}x${size[2]}`);
  if (!/<title[^>]*>[^<]+<\/title>/.test(svg)) throw new Error(`${name}: no <title>`);
  const outside = [...svg.matchAll(/(?:href|src)="([^"]*)"/g)].map((m) => m[1]).filter((u) => !u.startsWith("#") && !u.startsWith("data:"));
  if (outside.length) throw new Error(`${name}: references outside the file: ${outside.slice(0, 3).join(", ")}`);
  let images = 0;
  svg = svg.replace(/data:image\/png;base64,([A-Za-z0-9+/=]+)/g, (_, b64) => {
    images++;
    return `data:image/png;base64,${recompress(Buffer.from(b64, "base64")).toString("base64")}`;
  });
  const dest = path.join(site, "assets", `${name}.svg`);
  fs.writeFileSync(dest, svg);
  console.log(`${name}.svg: ${images} embedded PNG, ${(svg.length / 1024).toFixed(0)} KiB`);
}
