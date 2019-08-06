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
let {generateType, generateTermSerializers} = require('typedefs-js')

let haskellCode = generateTermSerializers('haskell', '(name Bit (+ 1 1))')
console.log(haskellCode)
```

In the browser

```html
<script type="text/javascript" src="https://unpkg.com/typedefs-js"></script>

<script type="text/javascript">
let haskell = Typedefs. generateTermSerializers('haskell', '(name Bit (+ 1 1))')
console.log(haskell)
</script>
```

## API

### `generateType : String -> String -> Either String String`

Generate the type definitions in the target language the given typedef as a string. 

The first argument to this function is the backend name as a string:

- `haskell`
- `reasonml`
- `json` (only supports **closed** typedefs)

The second argument is the typedef string.

Errors are returned as a string on the `Left` value of the either as is customary.

### `generateTermSerializers : String -> String -> Either String String`

Generate code in the target language that serialize and deserialize the given typedef as a string. 

The first argument to this function is the backend name as a string:

- `haskell`
- `reasonml`
- `json` (only supports **closed** typedefs)

The second argument is the typedef string.

Errors are returned as a string on the `Left` value of the either as is customary.

## Publishing an update to npm

Be sure to bump the version in `package.json`. Then also run `npm i` to rebuild and update the `package-lock.json`, then commit and push and CI should publish the build to npm.
