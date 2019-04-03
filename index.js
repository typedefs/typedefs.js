let {parseType, generateCode} = require('./lib/typedefs.js')

function Idris_foldMaybe (onNothing, onJust, m) {
    return m['type'] == 0 ? onNothing() : onJust(m['$1'])
}

function parseType_ (sExpression) {
    let onNothing = () => undefined;
    let onJust = (x) => x;
    return Idris_foldMaybe(onNothing, onJust, parseType(sExpression))
}

module.exports = {
    parseType: parseType_,
    generateCode: generateCode
}