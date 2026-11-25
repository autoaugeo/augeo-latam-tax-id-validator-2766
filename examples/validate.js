'use strict';
// Usage example. Every ID below is synthetic (made up by the algorithm), never a real person's.
const { validate, parseCfdi } = require('../src/core.js');

const samples = [
  ['AR', 'cuit', '20-12345678-6'],
  ['CL', 'rut', '12.345.678-5'],
  ['MX', 'rfc', 'ABC010101AB1'],
  ['BR', 'cpf', '111.444.777-35'],
  ['BR', 'cnpj', '12.ABC.345/01DE-35'],
  ['CO', 'nit', '900000001-2'],
  ['PE', 'ruc', '20123456786'],
  ['MX', 'auto', 'ABC010101AB2'],
];

samples.forEach(function (s) {
  const r = validate(s[0], s[1], s[2]);
  console.log(s[0] + ' ' + r.type + ' ' + s[2] + ' -> ' + (r.valid ? 'valid format' : 'invalid: ' + r.reason));
});

const xml = '<cfdi:Comprobante xmlns:cfdi="http://www.sat.gob.mx/cfd/4" Version="4.0" Fecha="2026-01-15T10:30:00" SubTotal="100.00" Moneda="MXN" Total="116.00" TipoDeComprobante="I">' +
  '<cfdi:Emisor Rfc="ABC010101AB1" Nombre="EMPRESA SINTETICA" RegimenFiscal="601"/>' +
  '<cfdi:Receptor Rfc="ABCD8001011A9" UsoCFDI="G03"/>' +
  '<cfdi:Conceptos><cfdi:Concepto Descripcion="Servicio"/></cfdi:Conceptos></cfdi:Comprobante>';
const inv = parseCfdi(xml);
console.log('CFDI ok=' + inv.ok + ' version=' + inv.version + ' total=' + inv.total +
  ' emisor RFC valid=' + inv.emisor.rfc_check.valid + ' concepts=' + inv.concept_count);
console.log('warnings: ' + inv.warnings.join('; '));
