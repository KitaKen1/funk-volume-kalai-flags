// Check the actual public Lean4Web LSP server. Requires Node.js 22 or newer.
// Any error diagnostic or nonstandard final proof axiom makes this run fail.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';

const packageRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const args = process.argv.slice(2);
const sourcePath = path.resolve(args[0] ?? path.join(packageRoot, 'lean4web/FunkKalaiLean4Web.lean'));
const output = path.resolve(args[1] ?? path.join(packageRoot, 'lean/evidence/lean4web-live.json'));
const source = fs.readFileSync(sourcePath, 'utf8');
const sha = x => crypto.createHash('sha256').update(x).digest('hex');
const expectedLean = 'leanprover/lean4:v4.35.0-rc4';
const expectedMathlib = process.env.FUNK_LEAN4WEB_MATHLIB_REV ??
  '021ce68bf125a049beee22b3fc7664d78728e21d';
const roots = ['Funk.symmetricFunk_lower_bound', 'Funk.kalai_full_flags',
  'FunkVolume.symmetricFunkVolume', 'Funk.FormalConjectures.kalaiFullFlags'];
const allowed = new Set(['propext', 'Classical.choice', 'Quot.sound']);
const record = {format: 1, status: 'running', started_at: new Date().toISOString(),
  server: 'https://live.lean-lang.org/', project: 'MathlibDemo',
  source_sha256: sha(source), source_bytes: Buffer.byteLength(source),
  whole_file_submitted_to_lsp: true, errors: [], warnings: [], final_axioms: {}};
fs.mkdirSync(path.dirname(output), {recursive: true});
const save = () => fs.writeFileSync(output, JSON.stringify(record, null, 2) + '\n');
const get = async endpoint => {
  const response = await fetch(record.server + endpoint, {signal: AbortSignal.timeout(30000)});
  if (!response.ok) throw new Error(`HTTP ${response.status}: ${endpoint}`);
  return response.text();
};
let socket, deadline, heartbeat;
let diagnostics = [], processingEmpty = false, done = false;

async function finish(reason) {
  if (done) return;
  done = true;
  clearTimeout(deadline);
  clearInterval(heartbeat);
  record.finished_at = new Date().toISOString();
  record.errors = diagnostics.filter(d => d.severity === 1);
  record.warnings = diagnostics.filter(d => d.severity === 2);
  if (!reason) {
    try {
      const after = JSON.parse(await get('api/manifest/MathlibDemo'));
      if (after.packages.find(p => p.name === 'mathlib')?.rev !== expectedMathlib)
        reason = 'Public Mathlib pin changed during the check';
      if (sha(fs.readFileSync(sourcePath)) !== record.source_sha256)
        reason = 'Source file changed during the check';
    } catch (e) { reason = String(e); }
  }
  const complete = roots.every(name => Array.isArray(record.final_axioms[name]));
  const axiomsAllowed = Object.values(record.final_axioms).every(xs => xs.every(x => allowed.has(x)));
  record.status = !reason && complete && axiomsAllowed && processingEmpty && !record.errors.length
    ? 'passed' : 'failed';
  record.reason = reason ?? (record.status === 'passed' ? null : 'Errors, incomplete processing, or unpermitted axioms');
  record.processing_finished = processingEmpty;
  record.no_sorryAx = complete && axiomsAllowed;
  save();
  fs.writeFileSync(output.replace(/\.json$/, '-diagnostics.json'), JSON.stringify(diagnostics, null, 2) + '\n');
  console.log(`${record.status}: ${record.errors.length} errors, ${record.warnings.length} warnings, ` +
    `${Object.keys(record.final_axioms).length} final axiom reports. Record: ${output}`);
  if (record.status !== 'passed') process.exitCode = 1;
  socket?.close();
}

try {
  record.toolchain = (await get('api/toolchain/MathlibDemo')).trim();
  const manifestText = await get('api/manifest/MathlibDemo');
  const manifest = JSON.parse(manifestText);
  record.mathlib = manifest.packages.find(p => p.name === 'mathlib')?.rev;
  record.manifest_sha256 = sha(manifestText);
  if (record.toolchain !== expectedLean || record.mathlib !== expectedMathlib)
    throw new Error('Public project versions differ from the tested source pins');
  save();
  socket = new WebSocket('wss://live.lean-lang.org/websocket/MathlibDemo');
  const send = message => socket.send(JSON.stringify({jsonrpc: '2.0', ...message}));
  deadline = setTimeout(() => finish('Public server timed out after 30 minutes'), 30 * 60 * 1000);
  heartbeat = setInterval(() => {
    console.log(`Public server: processing; final reports ${Object.keys(record.final_axioms).length}/${roots.length}`);
  }, 30000);
  socket.addEventListener('open', () => send({id: 1, method: 'initialize', params: {
    processId: null, rootUri: 'file:///MathlibDemo',
    capabilities: {textDocument: {publishDiagnostics: {relatedInformation: true}}},
    initializationOptions: {hasWidgets: false}
  }}));
  socket.addEventListener('message', async event => {
    if (done) return;
    const message = JSON.parse(typeof event.data === 'string' ? event.data : await event.data.text());
    if (message.id === 1 && !message.method) {
      if (message.error) return finish('LSP initialization failed: ' + JSON.stringify(message.error));
      record.server_info = message.result?.serverInfo;
      send({method: 'initialized', params: {}});
      send({method: 'textDocument/didOpen', params: {textDocument: {
        uri: 'file:///MathlibDemo/MathlibDemo.lean', languageId: 'lean4', version: 1, text: source
      }}});
      save();
    } else if (message.id !== undefined && message.method) {
      send({id: message.id, result: message.method === 'workspace/configuration'
        ? (message.params?.items ?? []).map(() => ({})) : null});
    }
    if (message.method === 'textDocument/publishDiagnostics') {
      const incoming = message.params.diagnostics ?? [];
      diagnostics = message.params.isIncremental ? [...diagnostics, ...incoming] : incoming;
      for (const diagnostic of diagnostics) {
        const matches = [...diagnostic.message.matchAll(/'([^']+)' depends on axioms: \[([^\]]*)\]/g)];
        for (const [, name, values] of matches)
          if (roots.includes(name)) record.final_axioms[name] = values.split(',').map(s => s.trim()).filter(Boolean);
      }
      record.errors = diagnostics.filter(d => d.severity === 1);
      record.warnings = diagnostics.filter(d => d.severity === 2);
      save();
    }
    if (message.method === '$/lean/fileProgress') {
      processingEmpty = (message.params.processing ?? []).length === 0;
      record.processing_finished = processingEmpty;
      save();
    }
    if (roots.every(name => record.final_axioms[name]) && processingEmpty) await finish();
  });
  socket.addEventListener('error', event => finish('WebSocket error: ' + (event.message ?? 'unknown')));
  socket.addEventListener('close', () => {if (!done) finish('Connection closed before complete verification');});
} catch (e) {
  await finish(String(e));
}
