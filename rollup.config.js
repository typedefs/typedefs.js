const commonjs = require('rollup-plugin-commonjs')
const babel = require('rollup-plugin-babel')
const {terser} = require("rollup-plugin-terser")
const buildins = require('rollup-plugin-node-builtins')
const analyze = require('rollup-plugin-analyzer').plugin;

const isNode = process.env.NODE_ENV === 'node'
const isProduction = isNode || (process.env.NODE_ENV === 'production')

const plugins = [
    buildins(),
    commonjs(),
    babel(),
    terser(),
    analyze({
        limit: 20
    })
]

export default {
  input: "index.js",
  output: {
    exports: 'named',
    file: `dist/typedefs.min.js`,
      format: "umd",
      name: "Typedefs",
      sourcemap: true
  },
  plugins: plugins
};