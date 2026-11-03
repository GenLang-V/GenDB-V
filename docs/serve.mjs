#!/usr/bin/env node
// A static server for the site (no dependencies): node docs/serve.mjs [--port 8794] [--host 0.0.0.0]
// Serves docs/ read-only, as GitHub Pages does, gzip-compressed when the client accepts it.
import http from "node:http";
import fs from "node:fs";
import path from "node:path";
import zlib from "node:zlib";
import { fileURLToPath } from "node:url";

const root = path.dirname(fileURLToPath(import.meta.url));
const arg = (name, dflt) => {
  const i = process.argv.indexOf(name);
  return i > 0 ? process.argv[i + 1] : dflt;
};
const port = Number(arg("--port", process.env.PORT || 8794));
const host = arg("--host", "0.0.0.0");
const TYPES = {
  ".html": "text/html; charset=utf-8", ".js": "text/javascript; charset=utf-8", ".css": "text/css; charset=utf-8",
  ".json": "application/json", ".svg": "image/svg+xml", ".png": "image/png", ".woff2": "font/woff2", ".txt": "text/plain; charset=utf-8",
};

http.createServer((req, res) => {
  let p;
  try {
    p = decodeURIComponent(new URL(req.url, "http://x").pathname);
  } catch {
    res.writeHead(400).end();
    return;
  }
  if (p.endsWith("/")) p += "index.html";
  const file = path.normalize(path.join(root, p));
  if (!file.startsWith(root + path.sep)) {
    res.writeHead(403).end();
    return;
  }
  fs.readFile(file, (err, body) => {
    if (err) {
      res.writeHead(404, { "content-type": "text/plain" }).end("not found");
      return;
    }
    const type = TYPES[path.extname(file)] || "application/octet-stream";
    const headers = { "content-type": type, "cache-control": "no-cache" };
    if (/\bgzip\b/.test(req.headers["accept-encoding"] || "") && body.length > 1024 && !type.startsWith("font/")) {
      headers["content-encoding"] = "gzip";
      body = zlib.gzipSync(body, { level: 6 });
    }
    res.writeHead(200, headers).end(body);
  });
}).listen(port, host, () => console.log(`GenDB-V site: http://${host === "0.0.0.0" ? "localhost" : host}:${port}/`));
