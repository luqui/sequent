//Flatten (Hyp "union") [nat,real] [] ["U1","U2","U3"] Done Flatten (Hyp "U3") [union(real,nat),x] ["G1","G2","G3"] ["H2"] Exact (Hyp "H1") (Goal "G3") Flatten (Hyp "union") [real,nat] [] ["U1'","U2'","U3'"] Done Intro (Goal "G1") ["a"] ["K"] Flatten (Hyp "U2'") [a] ["G1"] ["Z"] Exact (Hyp "K") (Goal "G1") Done Exact (Hyp "Z") (Goal "H0") Done Intro (Goal "G2") ["a"] ["K"] Flatten (Hyp "U1'") [a] ["G1"] ["Z"] Exact (Hyp "K") (Goal "G1") Done Exact (Hyp "Z") (Goal "H0") Done Done Exact (Hyp "H2") (Goal "H0") Done
//----- JS -----
function (_hyps) {
  var _goals = {};
  var nat = _hyps.nat;
  var real = _hyps.real;
  var x = _hyps.x;
  var union = _hyps.union;
  var H1 = _hyps.H1;
  var _tmp = union(_adapt({  }, { X: nat, Y: real }, function (_hyps) {
    var _goals = {};
    return _goals;
  }()));
  var U1 = _tmp.H0
  var U2 = _tmp.H1
  var U3 = _tmp.H2
  var union_Enat_jreal_D_ounion = _tmp.union
  var _tmp = U3(_adapt({ G1: 'H0', G2: 'H1', G3: 'H2' }, { Z: union_Ereal_jnat_D_ounion, z: x }, function (_hyps) {
    var _goals = {};
    _goals.G3 = H1;
    var _tmp = union(_adapt({  }, { X: real, Y: nat }, function (_hyps) {
      var _goals = {};
      return _goals;
    }()));
    var U1_O47 = _tmp.H0
    var U2_O47 = _tmp.H1
    var U3_O47 = _tmp.H2
    var union_Ereal_jnat_D_ounion = _tmp.union
    _goals.G1 = function (_hyps) {
      var _goals = {};
      var a = _hyps.x;
      var K = _hyps.H0;
      var _tmp = U2_O47(_adapt({ G1: 'H0' }, { y: a }, function (_hyps) {
        var _goals = {};
        _goals.G1 = K;
        return _goals;
      }()));
      var Z = _tmp.H0
      _goals.H0 = Z;
      return _goals;
    };
    _goals.G2 = function (_hyps) {
      var _goals = {};
      var a = _hyps.y;
      var K = _hyps.H0;
      var _tmp = U1_O47(_adapt({ G1: 'H0' }, { x: a }, function (_hyps) {
        var _goals = {};
        _goals.G1 = K;
        return _goals;
      }()));
      var Z = _tmp.H0
      _goals.H0 = Z;
      return _goals;
    };
    return _goals;
  }()));
  var H2 = _tmp.H0
  _goals.H0 = H2;
  return _goals;
}
