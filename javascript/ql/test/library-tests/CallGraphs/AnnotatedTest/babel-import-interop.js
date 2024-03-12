function _interopRequireDefault(obj) {
    return obj && obj.__esModule ? obj : { default: obj };
}

function _interopRequireWildcard(obj) {
    if (obj && obj.__esModule) {
      return obj;
    } else {
      var newObj = {};
      if (obj != null) {
        for (var key in obj) {
          if (Object.prototype.hasOwnProperty.call(obj, key))
            newObj[key] = obj[key];
        }
      }
      newObj["default"] = obj;
      return newObj;
    }
}

function _interopDefault(ex) {
    return ex && typeof ex === "object" && "default" in ex ? ex["default"] : ex;
}

//
// Plain import
//
const ed = require('./babel-export1');
const defaultInstance1 = new ed.default.C();
/** calls:DefaultClass.m */
defaultInstance1.m();

const namedInstance1 = new ed.Named.C();
/** calls:NamedClass.m */
namedInstance1.m();

//
// _interopRequireDefault
//
const ed2 = _interopRequireDefault(ed);
const defaultInstance2 = new ed2.default.C();
/** calls:DefaultClass.m */
defaultInstance2.m();

const namedInstance2 = new ed2.Named.C();
/** calls:NamedClass.m */
namedInstance2.m();

//
// _interopRequireWildcard
//
const ed3 = _interopRequireWildcard(ed);
const defaultInstance3 = new ed3.default.C();
/** calls:DefaultClass.m */
defaultInstance3.m();

const namedInstance3 = new ed3.Named.C();
/** calls:NamedClass.m */
namedInstance3.m();

//
// _interopDefault
//
const ed4 = _interopDefault(ed);
const defaultInstance4 = new ed4.C();
/** calls:DefaultClass.m */
defaultInstance4.m();

const namedInstance4 = new ed4.Named.C();
/** calls:NONE */
namedInstance4.m();
