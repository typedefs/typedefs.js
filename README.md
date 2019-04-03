[![Build Status](https://travis-ci.com/typedefs/typedefs.js.svg?branch=master)](https://travis-ci.com/typedefs/typedefs.js)

# JS version of typedefs

Generated from [`ParserJS.idr`](https://github.com/typedefs/typedefs/blob/master/parser.js/ParserJS.idr)

## Example

```js
let {parseType, generateCode} = require('typedefs-js')

let ty = parseType(`
;; a bit
(name Bit (+ 1 1))
`)

let haskell = generateCode('haskell', ty)
```

## API

- `parseType : String -> (n ** TNamed n)`

Parse S-expression string to `TNamed`, returns `undefined` if it failed to parse the typedef.

- `generateCode : String -> (n ** TNamed n) -> String`

Translate `TNamed` into backend code. The first argument to this function is the backend name as a string:

- `haskell`
- `reasonml`
- `json` (only supports **closed** typedefs)
