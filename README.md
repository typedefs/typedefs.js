[![Build Status](https://travis-ci.com/typedefs/typedefs.js.svg?branch=master)](https://travis-ci.com/typedefs/typedefs.js)

# JS version of [Typedefs](https://typedefs.com)

Generated from [`ParserJS.idr`](https://github.com/typedefs/typedefs/blob/master/parser.js/ParserJS.idr).

- Published on npm as [`typedefs-js`](https://npm.im/typedefs-js), to install for Node run,
  ```
  npm install -s typedefs-js
  ```
- It is also available for the browser using the unpkg CDN, use the following magic HTML incantation.
  ```html
  <script type="text/javascript" src="https://unpkg.com/typedefs-js"></script>
  ```

## Usage example

For node

```js
let {parseType, generateCode} = require('typedefs-js')

let ty = parseType('(name Bit (+ 1 1))')
let haskellCode = generateCode('haskell', ty)
console.log(haskellCode)
```

In the browser

```html
<script type="text/javascript" src="https://unpkg.com/typedefs-js"></script>

<script type="text/javascript">
let ty = Typedefs.parseType('(name Bit (+ 1 1))')
let haskell = Typedefs.generateCode('haskell', ty)
console.log(haskell)
</script>
```

## API

### `parseType : String -> (n ** TNamed n)`

Parse S-expression string to `TNamed`, returns `undefined` if it failed to parse the typedef.

### `generateCode : String -> (n ** TNamed n) -> String`

Translate `TNamed` into backend code. The first argument to this function is the backend name as a string:

- `haskell`
- `reasonml`
- `json` (only supports **closed** typedefs)

## Publishing an update to npm

Be sure to bump the version in `package.json`. Then also run `npm i` to rebuild and update the `package-lock.json`, then commit and push and CI should publish the build to npm.