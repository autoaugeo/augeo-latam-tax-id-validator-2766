'use strict';
/*
 * LatAm tax-ID validators + CFDI header parser. Plain CommonJS, zero dependencies,
 * no network, no file access. Every validator checks FORMAT and CHECK DIGITS only:
 * it does not confirm that an ID is registered or active with any tax authority.
 *
 * Algorithm sources (plain-text citations, as published by each tax authority):
 *  - AR CUIT/CUIL: modulo 11 with weights 5,4,3,2,7,6,5,4,3,2 (AFIP/ARCA)
 *  - CL RUT:       modulo 11 with weights 2..7 repeating (SII)
 *  - MX RFC:       modulo 11 homoclave check character (SAT)
 *  - MX CURP:      18-character layout with check digit (RENAPO)
 *  - BR CPF:       two modulo 11 check digits (Receita Federal)
 *  - BR CNPJ:      two modulo 11 check digits, alphanumeric format (Receita Federal)
 *  - CO NIT:       modulo 11 with prime weights (DIAN)
 *  - PE RUC:       modulo 11 check digit (SUNAT)
 */

const COUNTRY_TYPES = {
  AR: ['cuit', 'cuil'],
  CL: ['rut'],
  MX: ['rfc', 'curp'],
  BR: ['cpf', 'cnpj'],
  CO: ['nit'],
  PE: ['ruc'],
};

function blank(country, type, input) {
  return {
    input: input,
    country: country,
    type: type,
    normalized: null,
    valid: false,
    reason: null,
    check_digit_expected: null,
    check_digit_found: null,
    flags: [],
  };
}

function fail(r, reason) {
  r.valid = false;
  r.reason = reason;
  return r;
}

function pass(r) {
  r.valid = true;
  r.reason = null;
  return r;
}

// Upper-case and drop the separators people type (spaces, dots, hyphens, slashes).
function normalize(value) {
  return String(value).toUpperCase().replace(/[\s.\-\/_ ]/g, '');
}

// Returns an error text when `n` is not exactly `len` digits, else null.
function digitsProblem(n, len) {
  if (!/^\d+$/.test(n)) return 'contains characters other than digits';
  if (n.length !== len) return 'expected ' + len + ' digits, found ' + n.length;
  return null;
}

function weightedSum(values, weights) {
  let s = 0;
  for (let i = 0; i < values.length; i++) s += values[i] * weights[i];
  return s;
}

function digitsOf(str) {
  return str.split('').map(Number);
}

function daysIn(mm) {
  return [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][mm - 1];
}

// yy/mm/dd are strings. Century is unknown, so Feb 29 is accepted for any year.
function dateProblem(s6) {
  const mm = Number(s6.slice(2, 4));
  const dd = Number(s6.slice(4, 6));
  if (mm < 1 || mm > 12) return 'invalid month ' + s6.slice(2, 4) + ' in the date part';
  if (dd < 1 || dd > daysIn(mm)) return 'invalid day ' + s6.slice(4, 6) + ' in the date part';
  return null;
}

// ---- AR CUIT / CUIL: 11 digits, prefix, mod 11 with weights 5,4,3,2,7,6,5,4,3,2 ----
const CUIT_PREFIXES = ['20', '23', '24', '27', '30', '33', '34'];
const CUIT_WEIGHTS = [5, 4, 3, 2, 7, 6, 5, 4, 3, 2];

function checkCuit(n, r) {
  const p = digitsProblem(n, 11);
  if (p) return fail(r, p);
  r.check_digit_found = n[10];
  if (CUIT_PREFIXES.indexOf(n.slice(0, 2)) < 0) {
    return fail(r, 'prefix ' + n.slice(0, 2) + ' is not a CUIT/CUIL type code (20, 23, 24, 27, 30, 33, 34)');
  }
  const m = weightedSum(digitsOf(n.slice(0, 10)), CUIT_WEIGHTS) % 11;
  const c = 11 - m;
  if (c === 10) {
    return fail(r, 'check digit computes to 10, so no valid CUIT/CUIL exists for these first 10 digits');
  }
  const expected = String(c === 11 ? 0 : c);
  r.check_digit_expected = expected;
  if (expected !== r.check_digit_found) return fail(r, 'check digit mismatch');
  return pass(r);
}

// ---- CL RUT: body 6-8 digits, mod 11 with weights 2..7 cycling from the right; 10 -> K, 11 -> 0 ----
function checkRut(n, r) {
  if (!/^[0-9]+[0-9K]$/.test(n)) return fail(r, 'contains characters other than digits and a final K');
  const body = n.slice(0, -1);
  r.check_digit_found = n.slice(-1);
  if (body.length < 6 || body.length > 8) {
    return fail(r, 'RUT body must have 6 to 8 digits, found ' + body.length);
  }
  const ds = digitsOf(body).reverse();
  let s = 0;
  for (let i = 0; i < ds.length; i++) s += ds[i] * (2 + (i % 6));
  const c = 11 - (s % 11);
  const expected = c === 11 ? '0' : c === 10 ? 'K' : String(c);
  r.check_digit_expected = expected;
  if (expected !== r.check_digit_found) return fail(r, 'check digit mismatch');
  return pass(r);
}

// ---- MX RFC: 12 (moral) / 13 (fisica) chars; verifier = mod 11 over the SAT alphabet ----
// Moral RFCs are left-padded with a space to 13 chars; the first 12 are weighted 13..2.
// 11 - (sum mod 11): 11 -> '0', 10 -> 'A'. Cross-checked by hand on SAT970701NN3 (see tests).
const RFC_ALPHABET = '0123456789ABCDEFGHIJKLMN&OPQRSTUVWXYZ ' + 'Ñ';
const RFC_GENERIC = ['XAXX010101000', 'XEXX010101000'];

function checkRfc(n, r) {
  if (!/^[A-ZÑ0-9&]+$/.test(n)) return fail(r, 'contains characters outside A-Z, Ñ, & and digits');
  if (n.length !== 12 && n.length !== 13) {
    return fail(r, 'RFC must have 12 (company) or 13 (person) characters, found ' + n.length);
  }
  r.check_digit_found = n.slice(-1);
  if (RFC_GENERIC.indexOf(n) >= 0) {
    r.flags.push('generic_rfc');
    return pass(r);
  }
  const nameLen = n.length === 12 ? 3 : 4;
  if (!/^[A-ZÑ&]+$/.test(n.slice(0, nameLen))) {
    return fail(r, 'the first ' + nameLen + ' characters must be letters');
  }
  if (!/^\d{6}$/.test(n.slice(nameLen, nameLen + 6))) return fail(r, 'the date part must be 6 digits (YYMMDD)');
  const dp = dateProblem(n.slice(nameLen, nameLen + 6));
  if (dp) return fail(r, dp);
  if (!/^[A-Z0-9]{3}$/.test(n.slice(-3))) return fail(r, 'the last 3 characters (homoclave) must be letters or digits');
  const padded = n.length === 12 ? ' ' + n : n;
  let s = 0;
  for (let i = 0; i < 12; i++) s += RFC_ALPHABET.indexOf(padded[i]) * (13 - i);
  const c = 11 - (s % 11);
  const expected = c === 11 ? '0' : c === 10 ? 'A' : String(c);
  r.check_digit_expected = expected;
  if (expected !== r.check_digit_found) return fail(r, 'check digit mismatch');
  return pass(r);
}

// ---- MX CURP: 18 chars; verifier = (10 - sum(value*(18-i)) mod 10) mod 10 ----
// Value alphabet: 0-9, A-N = 10-23, Ñ = 24, O-Z = 25-36.
const CURP_ALPHABET = '0123456789ABCDEFGHIJKLMNÑOPQRSTUVWXYZ';
const CURP_STATES = ('AS BC BS CC CL CM CS CH DF DG GT GR HG JC MC MN MS NT NL OC PL QT QR SP SL SR TC TS TL VZ YN ZS NE').split(' ');

function checkCurp(n, r) {
  if (!/^[A-ZÑ0-9]+$/.test(n)) return fail(r, 'contains characters outside A-Z, Ñ and digits');
  if (n.length !== 18) return fail(r, 'CURP must have 18 characters, found ' + n.length);
  r.check_digit_found = n[17];
  if (!/^[A-Z]{4}\d{6}[HMX][A-Z]{2}[A-Z]{3}[A-Z0-9]\d$/.test(n)) {
    return fail(r, 'does not match the CURP layout (4 letters, 6-digit date, sex H/M/X, 2-letter state, 3 letters, 1 letter or digit, 1 digit)');
  }
  const dp = dateProblem(n.slice(4, 10));
  if (dp) return fail(r, dp);
  if (CURP_STATES.indexOf(n.slice(11, 13)) < 0) return fail(r, 'unknown state code ' + n.slice(11, 13));
  let s = 0;
  for (let i = 0; i < 17; i++) s += CURP_ALPHABET.indexOf(n[i]) * (18 - i);
  const expected = String((10 - (s % 10)) % 10);
  r.check_digit_expected = expected;
  if (expected !== r.check_digit_found) return fail(r, 'check digit mismatch');
  return pass(r);
}

// ---- BR CPF: 11 digits, two mod 11 digits (weights 10..2 then 11..2), all-equal rejected ----
function mod11Dv(values, firstWeight) {
  let s = 0;
  for (let i = 0; i < values.length; i++) s += values[i] * (firstWeight - i);
  const m = s % 11;
  return m < 2 ? 0 : 11 - m;
}

function checkCpf(n, r) {
  const p = digitsProblem(n, 11);
  if (p) return fail(r, p);
  r.check_digit_found = n.slice(9);
  if (/^(\d)\1{10}$/.test(n)) return fail(r, 'all digits are equal, which is not a valid CPF');
  const ds = digitsOf(n);
  const d1 = mod11Dv(ds.slice(0, 9), 10);
  const d2 = mod11Dv(ds.slice(0, 9).concat([d1]), 11);
  r.check_digit_expected = String(d1) + String(d2);
  if (r.check_digit_expected !== r.check_digit_found) return fail(r, 'check digit mismatch');
  return pass(r);
}

// ---- BR CNPJ: 12 base chars + 2 digits; mod 11, weights 5,4,3,2,9,8,7,6,5,4,3,2 then 6,5,...,2 ----
// Alphanumeric CNPJ (Receita Federal, IN RFB 2.229/2024, in force from July 2026): every
// character counts as its ASCII code minus 48 (digits keep their value, A=17 ... Z=42); the
// two check digits stay numeric and the modulo/weights are unchanged. Source: Receita Federal
// "CNPJ alfanumerico" perguntas e respostas (URL in the header), which works the example
// 12.ABC.345/01DE-35.
const CNPJ_W1 = [5, 4, 3, 2, 9, 8, 7, 6, 5, 4, 3, 2];
const CNPJ_W2 = [6, 5, 4, 3, 2, 9, 8, 7, 6, 5, 4, 3, 2];

function cnpjDv(values, weights) {
  const m = weightedSum(values, weights) % 11;
  return m < 2 ? 0 : 11 - m;
}

function checkCnpj(n, r) {
  if (!/^[0-9A-Z]+$/.test(n)) return fail(r, 'contains characters outside 0-9 and A-Z');
  if (n.length !== 14) return fail(r, 'expected 14 characters, found ' + n.length);
  if (!/^[0-9A-Z]{12}\d{2}$/.test(n)) return fail(r, 'the last 2 characters (check digits) must be digits');
  r.check_digit_found = n.slice(12);
  if (/^(.)\1{13}$/.test(n)) return fail(r, 'all characters are equal, which is not a valid CNPJ');
  const vals = n.slice(0, 12).split('').map(function (ch) { return ch.charCodeAt(0) - 48; });
  const d1 = cnpjDv(vals, CNPJ_W1);
  const d2 = cnpjDv(vals.concat([d1]), CNPJ_W2);
  r.check_digit_expected = String(d1) + String(d2);
  if (/[A-Z]/.test(n)) r.flags.push('alphanumeric_cnpj');
  if (r.check_digit_expected !== r.check_digit_found) return fail(r, 'check digit mismatch');
  return pass(r);
}

// ---- CO NIT: body 5-15 digits + 1 check digit; DIAN prime weights from the right ----
// remainder = sum mod 11; check digit = remainder if < 2, else 11 - remainder.
const NIT_WEIGHTS = [3, 7, 13, 17, 19, 23, 29, 37, 41, 43, 47, 53, 59, 67, 71];

function checkNit(n, r) {
  if (!/^\d+$/.test(n)) return fail(r, 'contains characters other than digits');
  if (n.length < 6 || n.length > 16) {
    return fail(r, 'NIT must have 5 to 15 digits plus a check digit, found ' + n.length + ' digits in total');
  }
  const body = digitsOf(n.slice(0, -1)).reverse();
  r.check_digit_found = n.slice(-1);
  const m = weightedSum(body, NIT_WEIGHTS) % 11;
  r.check_digit_expected = String(m < 2 ? m : 11 - m);
  if (r.check_digit_expected !== r.check_digit_found) return fail(r, 'check digit mismatch');
  return pass(r);
}

// ---- PE RUC: 11 digits, prefix 10/15/17/20, weights 5,4,3,2,7,6,5,4,3,2, (11 - sum mod 11) mod 10 ----
const RUC_PREFIXES = ['10', '15', '17', '20'];

function checkRuc(n, r) {
  const p = digitsProblem(n, 11);
  if (p) return fail(r, p);
  r.check_digit_found = n[10];
  if (RUC_PREFIXES.indexOf(n.slice(0, 2)) < 0) {
    return fail(r, 'prefix ' + n.slice(0, 2) + ' is not a RUC prefix (10, 15, 17, 20)');
  }
  const m = weightedSum(digitsOf(n.slice(0, 10)), CUIT_WEIGHTS) % 11;
  r.check_digit_expected = String((11 - m) % 10);
  if (r.check_digit_expected !== r.check_digit_found) return fail(r, 'check digit mismatch');
  return pass(r);
}

const CHECKERS = {
  cuit: checkCuit, cuil: checkCuit, rut: checkRut, rfc: checkRfc, curp: checkCurp,
  cpf: checkCpf, cnpj: checkCnpj, nit: checkNit, ruc: checkRuc,
};

// Picks the ID type from the country and the shape of the normalized value.
function detect(country, n) {
  if (country === 'AR') return 'cuit';
  if (country === 'CL') return 'rut';
  if (country === 'CO') return 'nit';
  if (country === 'PE') return 'ruc';
  if (country === 'BR') {
    if (n.length === 11) return 'cpf';
    if (n.length === 14) return 'cnpj';
    return null;
  }
  if (country === 'MX') {
    if (n.length === 18) return 'curp';
    if (n.length === 12 || n.length === 13) return 'rfc';
    return null;
  }
  return null;
}

function validate(country, type, value) {
  const c = typeof country === 'string' ? country.trim().toUpperCase() : '';
  let t = typeof type === 'string' ? type.trim().toLowerCase() : 'auto';
  if (t === '') t = 'auto';
  const r = blank(c, t, value);
  try {
    if (typeof value !== 'string' && typeof value !== 'number') return fail(r, 'input must be a string');
    const n = normalize(value);
    r.normalized = n;
    if (!COUNTRY_TYPES[c]) {
      return fail(r, 'unsupported country "' + c + '"; supported: ' + Object.keys(COUNTRY_TYPES).join(', '));
    }
    if (t === 'auto') {
      const d = detect(c, n);
      if (!d) return fail(r, 'could not detect the ID type from its length; set the type explicitly (' + COUNTRY_TYPES[c].join(', ') + ')');
      t = d;
      r.type = d;
    }
    if (COUNTRY_TYPES[c].indexOf(t) < 0) {
      return fail(r, 'type "' + t + '" is not supported for ' + c + '; supported: ' + COUNTRY_TYPES[c].join(', '));
    }
    if (n === '') return fail(r, 'empty value');
    return CHECKERS[t](n, r);
  } catch (e) {
    return fail(r, 'unexpected error while validating');
  }
}

// ---- CFDI 3.3 / 4.0 header parser (regex based, no XML library) ----
// Reads the Comprobante, Emisor, Receptor and TimbreFiscalDigital attributes and counts
// Concepto elements. It does NOT verify the SAT seal (Sello/SelloSAT/certificate) and does
// not query SAT: a parsed document is not proof that the invoice is valid or was stamped.
const MAX_XML_CHARS = 5000000;

function decodeEntities(s) {
  return s.replace(/&(?:#x([0-9a-fA-F]+)|#(\d+)|(lt|gt|amp|quot|apos));/g, function (m, hex, dec, name) {
    if (name) return { lt: '<', gt: '>', amp: '&', quot: '"', apos: "'" }[name];
    const cp = hex ? parseInt(hex, 16) : parseInt(dec, 10);
    try { return String.fromCodePoint(cp); } catch (e) { return m; }
  });
}

function parseAttrs(s) {
  const out = {};
  const re = /([A-Za-z_][\w:.-]*)\s*=\s*(?:"([^"]*)"|'([^']*)')/g;
  let m;
  while ((m = re.exec(s)) !== null) out[m[1]] = decodeEntities(m[2] !== undefined ? m[2] : m[3]);
  return out;
}

// Attributes of the first element called `name` (any namespace prefix), or null.
function findTag(xml, name) {
  const re = new RegExp('<(?:[A-Za-z_][\\w.-]*:)?' + name + '(?=[\\s/>])((?:"[^"]*"|\'[^\']*\'|[^>"\'])*)>');
  const m = re.exec(xml);
  return m ? parseAttrs(m[1]) : null;
}

function pick(o, k) {
  return o && o[k] !== undefined ? o[k] : null;
}

function cfdiFail(reason) {
  return { ok: false, reason: reason };
}

function parseCfdi(xmlString) {
  try {
    if (typeof xmlString !== 'string') return cfdiFail('input must be an XML string');
    let xml = xmlString.replace(/^﻿/, '').trim();
    if (xml === '') return cfdiFail('empty input');
    if (xml.length > MAX_XML_CHARS) return cfdiFail('input is larger than 5,000,000 characters');
    if (xml[0] !== '<') return cfdiFail('input does not look like XML');
    if (/<!DOCTYPE|<!ENTITY/i.test(xml)) return cfdiFail('DOCTYPE and ENTITY declarations are not accepted');
    xml = xml.replace(/<!--[\s\S]*?-->/g, '');

    const root = /<((?:[A-Za-z_][\w.-]*:)?)Comprobante(?=[\s/>])/.exec(xml);
    if (!root) return cfdiFail('no Comprobante element found');
    const prefix = root[1];
    if (!new RegExp('</' + prefix + 'Comprobante\\s*>').test(xml)) {
      return cfdiFail('Comprobante element is not closed (truncated or malformed XML)');
    }
    const comp = findTag(xml, 'Comprobante');
    const version = pick(comp, 'Version');
    if (version !== '3.3' && version !== '4.0') {
      if (version === null && pick(comp, 'version')) {
        return cfdiFail('unsupported CFDI version ' + comp.version + '; only 3.3 and 4.0 are supported');
      }
      return cfdiFail(version === null ? 'Comprobante has no Version attribute' : 'unsupported CFDI version ' + version + '; only 3.3 and 4.0 are supported');
    }
    const emisor = findTag(xml, 'Emisor');
    const receptor = findTag(xml, 'Receptor');
    if (!emisor) return cfdiFail('no Emisor element found');
    if (!receptor) return cfdiFail('no Receptor element found');
    const timbre = findTag(xml, 'TimbreFiscalDigital');
    const conceptos = xml.match(/<(?:[A-Za-z_][\w.-]*:)?Concepto(?=[\s/>])/g);

    const warnings = [];
    ['Fecha', 'SubTotal', 'Total', 'Moneda', 'TipoDeComprobante'].forEach(function (k) {
      if (pick(comp, k) === null) warnings.push('Comprobante has no ' + k + ' attribute');
    });
    if (pick(emisor, 'Rfc') === null) warnings.push('Emisor has no Rfc attribute');
    if (pick(receptor, 'Rfc') === null) warnings.push('Receptor has no Rfc attribute');
    if (!timbre || pick(timbre, 'UUID') === null) warnings.push('no TimbreFiscalDigital UUID found (document may not be stamped)');

    const eRfc = pick(emisor, 'Rfc');
    const rRfc = pick(receptor, 'Rfc');
    return {
      ok: true,
      version: version,
      serie: pick(comp, 'Serie'),
      folio: pick(comp, 'Folio'),
      fecha: pick(comp, 'Fecha'),
      subtotal: pick(comp, 'SubTotal'),
      total: pick(comp, 'Total'),
      moneda: pick(comp, 'Moneda'),
      tipo_de_comprobante: pick(comp, 'TipoDeComprobante'),
      emisor: {
        rfc: eRfc,
        nombre: pick(emisor, 'Nombre'),
        regimen_fiscal: pick(emisor, 'RegimenFiscal'),
        rfc_check: eRfc === null ? null : validate('MX', 'rfc', eRfc),
      },
      receptor: {
        rfc: rRfc,
        nombre: pick(receptor, 'Nombre'),
        uso_cfdi: pick(receptor, 'UsoCFDI'),
        regimen_fiscal: pick(receptor, 'RegimenFiscalReceptor'),
        domicilio_fiscal: pick(receptor, 'DomicilioFiscalReceptor'),
        rfc_check: rRfc === null ? null : validate('MX', 'rfc', rRfc),
      },
      uuid: pick(timbre, 'UUID'),
      fecha_timbrado: pick(timbre, 'FechaTimbrado'),
      concept_count: conceptos ? conceptos.length : 0,
      warnings: warnings,
      seal_verified: false,
      notice: 'Structure and RFC check digits only. The SAT seal was not verified and SAT was not queried.',
    };
  } catch (e) {
    return cfdiFail('unexpected error while parsing');
  }
}

module.exports = { validate, parseCfdi, COUNTRY_TYPES };
