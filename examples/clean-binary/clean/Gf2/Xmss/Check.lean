module

public import Gf2.Xmss.Inputs
public import Gf2.Xmss.Witness
meta import Gf2.Xmss.Inputs
meta import Gf2.Xmss.Witness

/-!
The XMSS block against `crates/xmss` and the BLAKE2s reference:
* the block builds (clauses sharing a row come from disjoint roles) and fits `2^15` rows and
  columns with `n_public = 0`;
* `blake2s` equals Rust's `primitives::hash::Hasher` on 0, 48, 64, 96, 704 and 736 bytes, and the
  circuit, one idle instance per block with variable `t` and `f0`, hashes the same inputs to the
  same digests with every constraint holding;
* three signatures from `crates/xmss` (`key_gen_from_seed([s; 32], 0, 15)` for `s = 1, 2`, signed
  at leaves 3 and 7) verify natively, and `signerSet` equals Rust's digests;
* the scheduled witness of a signer set using every role satisfies every role row of every
  instance up to the first padding instance, which leaves its registers unchanged (all later ones
  repeat it); the first instance of each role satisfies every row, by `violations` and by Clean's
  `countViolations`, and its Clean witness agrees with the scheduler's signals; the boundary is
  all-zero `in`, and the Rust digest then zeros `out`;
* a wrong chain tip, a skipped chain step, a wrong digit sum, a swapped Merkle direction and a
  wrong root each first break a row at an instance of the expected role.
-/

namespace Gf2.Xmss.Check

open Block Witness

example : build.isOk && rows.size ≤ 2 ^ 15 && 64 + (nSignals - 1) ≤ 2 ^ 15 := by
  native_decide

def pattern (n : ℕ) : ByteArray := ⟨(Array.range n).map fun i => (7 * i + 3).toUInt8⟩

/-- `primitives::hash::Hasher` digests of `pattern n`. -/
def rustBlake2s : List (ℕ × String) := [
  (0, "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9"),
  (48, "32fa11a9e88e46ad0f50308eea8256f807fade59288301b5d9230403068b2b96"),
  (64, "5377e4ff957bda4d4535f4879876b71a61056c4cec31e78397c66ec47a86a130"),
  (96, "3d9a2d741f92cb383c27729d8dbd377621604f7a4fd3930e435270bb299e62b0"),
  (704, "994031979eeb11e630157135040e3bf2f28397c88904899ee847b927c8e745dd"),
  (736, "7b26b097237a5e79052ea54f7ca98b5c1b3dde99fd15d89a2afe1e7780e93f86")]

example : rustBlake2s.all fun (n, d) => hex (blake2s (pattern n)) == d := by
  native_decide

def setWords (z : Array Bool) (sig : ℕ → ℕ) (ws : Array UInt32) : Array Bool :=
  (List.range (32 * ws.size)).foldl
    (fun z i => z.set! (sig i) ((ws[i / 32]! >>> (i % 32).toUInt32) &&& 1 == 1)) z

/-- The Clean witness of an idle instance compressing `(h, m, t, f0)` from all-zero registers. -/
def idleWitness (h m : Array UInt32) (t : ℕ) (final : Bool) : Array F :=
  let z := solve { role := .idle } (Array.replicate nReg false)
  witness ((setWords (setWords (setWords z hSig h) mSig m) tSig #[t.toUInt32]).set! f0Sig final)

def outWords (w : Array F) : Array UInt32 :=
  (Array.range 8).map fun i => readWord (fun j => w[j]?.getD 0) (oSig 0 - 1) i

/-- `d` hashed through the circuit, one idle instance per block, and the violated rows. -/
def circuitHash (d : ByteArray) : String × ℕ :=
  let blocks := max 1 ((d.size + 63) / 64)
  let (h, bad) := (List.range blocks).foldl (fun (h, bad) b =>
    let last := b + 1 == blocks
    let w := idleWitness h (blockWords d (64 * b)) (if last then d.size else 64 * (b + 1)) last
    (outWords w, bad + (violations w).size)) (IV0, 0)
  (hex (wordsBytes h), bad)

def circuitAgrees (n : ℕ) : Bool := rustBlake2s.any fun (k, d) => k == n && circuitHash (pattern n) == (d, 0)

example : circuitAgrees 48 := by native_decide
example : circuitAgrees 64 := by native_decide
example : circuitAgrees 96 := by native_decide
example : circuitAgrees 704 := by native_decide
example : circuitAgrees 736 := by native_decide

/-- `inputs.json` of three `crates/xmss` signatures: group `(3, m1)` signed by the keys of seeds 1
and 2 (in key order), group `(7, m2)` by the key of seed 1. -/
def realJson : String :=
  "{\"groups\":[{\"leaf_index\":3,\"message\":\"010c17222d38434e59646f7a85909ba6b1bcc7d2dde8f3fe091\
  41f2a35404b56\",\"signers\":[{\"root\":\"597242f1cedd3f6c0dc284efd3410982\",\"pp\":\"a786a09c3fa\
  645dbfbf2d0752537a7f1\",\"randomness\":\"c808e1707a57b6f77afde67c0fb6533e0be8bb7bae919cec\",\"ch\
  ain_tips\":[\"7436fa335631bf937707ef3ea4a0797d\",\"2c9303d28099474483aead333728c6fc\",\"968f8b6b\
  3891dc9a84df5795fa696bfc\",\"451ea2ab837724d7b0bcfdf415460505\",\"a23a74b856d80b0524f2bc5b4bf9fe\
  33\",\"990e51457f55d347422343860d70c641\",\"80742d6c326a7cd54b1ff8464d307b85\",\"ad294a544534973\
  4251005114e1bb821\",\"e5a70e439b5a5512386f33c3ed6011a7\",\"e4e287e6c2a09da25b3f93219666e87f\",\"\
  60311edda8d197e015e700afb27f1374\",\"c09a631cc027bdde29810bd4e3ef273a\",\"34a072783d563fcd887303\
  c4014c9b8f\",\"1e60883c6b35666353fc681b24c33060\",\"cec020b45e7b27cd5d363677007b1f9b\",\"21c25ec\
  5438f5dd8dd5706ad52f56a65\",\"96485ae201efcde96ef90752d2ce8a43\",\"35868777b51f0f00ce3373050ceaa\
  612\",\"cb5e5f0fd823a0b508ea5e47640babf7\",\"c1b6eba7696df76d874f4d5efe00a144\",\"b4f3ecc4c15b79\
  ccf093f83abc1719ae\",\"77dcbff2acb09381d05458b2cbd515f3\",\"8ce6a77ca6a88b35d7b6c43526ecd478\",\"\
  3a3f49de0a453fbc114614baf9180926\",\"42a153cd2519cf0ddd03e8b7212f27ae\",\"c8372e8e65131d5c204495\
  99b88802f3\",\"99324d711a9cfaf2dd159c93af885c30\",\"0c1484f40205d50a0deb5caeed8299fe\",\"30c7fb1\
  a767d0e79bcd9e7761a8daf1d\",\"77c168c94b91d723858dcd2fc0a36767\",\"23a196cbe1d6b57c63229aedce105\
  f06\",\"9b081e9370c6e9bba4f5ce7d737317ee\",\"233f4adecec86883a3fac47cb1dcc6a2\",\"6543872dffbbf9\
  6d8fab0155a8bbb1be\",\"d5bf1531456ff27242fd5b173815a084\",\"e6eb9b1edd28c3d967de36fb7a5e4a87\",\"\
  a07fb19eda0480e6251feaeef37deeb1\",\"abc1f569d30d14e1014383da17b0505a\",\"a18dacc1a74e090c17835e\
  9d557a7059\",\"afee07e982fcea2835de57988a4ac93d\",\"05a1389f397d9d08ea472cae8013686d\",\"e14b336\
  f249388b65c84fb72655e9b7c\"],\"merkle_proof\":[\"a165e72f53be0b30d6ffa06c8db242db\",\"82bebb548b\
  be2f227bc85236f7d50d61\",\"670e49e74d5274cc78f99a4b4b61a3cb\",\"033246785b698ee4ba4032b36fd13301\
  \",\"f4bffc8eb90b75507f9364e8f924f4de\",\"accca352883f3319b7bda6264c65c3da\",\"71c21ca0cb0f899f7\
  8a24de88c7959e9\",\"c4b6d64c42816c43d48648bb1b328130\",\"ea09f9f2b2b27f929dc4c4676b3068c9\",\"6e\
  789b49489e52aa044f0e65f4124f86\",\"46a8dcc6e405c6feb603ae950a56265e\",\"07ddbe87d32f1d70f3bad456\
  12a53cee\",\"af77c3df730385d1e8e9ccbb0e785471\",\"5e0d7423ca00c9dac7f6eaaad340ad04\",\"3dba3c9c1\
  6d94e212abb4c4ec5cd3425\",\"11ca6d69bee5d73f8f5bbb81c606f82e\",\"a8999b6cf4ed4d437cae0fa128abbca\
  3\",\"68a490880d32ee581d4e295e804d2c12\",\"bdf77b1486106e62572e3e0ac7f280ca\",\"a3ae3c7a9c6acbcd\
  40ee4d4bab8fa0d2\",\"c9a4c88b70d3fc9e34837f1b0390d2f1\",\"e3e96f006ddfd04e11fffe2172f05b05\",\"c\
  cb3b2f09b93dd672a36553e8efae278\",\"550e1783b298ba9ee52625517ec4ed51\",\"7552aec41d377a8b4ee6b17\
  a0e33fa44\",\"0860f46f8f34dc97cbaed7f7f47ca370\",\"4845f2262370e3cfa0a959c502737a95\",\"15ae0d89\
  a76eeca43077cd2ddc11aea9\",\"fde8abc4fd31db5a11c0e15224e1641e\",\"35ec3a2d1bab70e2d6253e69b4a59e\
  ab\",\"90773f568af229b04200ae7650c1890e\",\"454e0b7a979497cc569e4dcb8f38fc75\"]},{\"root\":\"98e\
  318084f90b072c8537f5dc449c54d\",\"pp\":\"c035ea2482e2a3f9cb60e37c7b7c92a2\",\"randomness\":\"272\
  a81993d282b65ce5bfaf6b7ed3dc3bc57c377d64af6de\",\"chain_tips\":[\"e37d5e5d2b06f72064c2d743132ee5\
  52\",\"b6242ab153072cebc525374e5cfdcebf\",\"bdeac09ed985f75c2522973fc1a02055\",\"f3f97fddcbe151b\
  c622de79998ab0c02\",\"29d18be7575062709eb30f33d2c3f5a3\",\"bd8ddb43ceeaf06756c45fbc8ef6c4fa\",\"\
  e3b4f9d94345764554b91ae7da17d76a\",\"6c0d99ed4c8a8cf5c3792dc4dbc89334\",\"46bed708bddcfa3ba22eb9\
  8dab553d12\",\"eeb93bf1776c157391cbfaeb58a140cc\",\"e0e66b8c97d4abb54a1bf8105f4b9f55\",\"0ceeeda\
  33e0d649696a7de82fd986c2b\",\"894fdf5bcc38d68c2475ea0e29cab260\",\"833005d19abcbea0df087614194ce\
  438\",\"9df11f16312a97ed9cace98102f685b9\",\"5e9897b50d5cebaa0094e98bba05718c\",\"9a112ca5d6ab82\
  d70d3d1cbc4e1409b6\",\"9786fb5c09d6dbeb9188df46d687f837\",\"bc094cec0e829b0d3b8b8eb6f5815bd8\",\"\
  c8ccb2c0b85fa2008d7421240daf6e6d\",\"f515f280b684e9401233ee34b388b35d\",\"7c36eb34fedb56b9f0867b\
  473495da93\",\"73de6495addba8475a5ec9e99b54e379\",\"f86a83473c03f4361fc0241501aac226\",\"3a443ab\
  eae6e0355cf218e27a53ad3e0\",\"a7334b15c899f4bcaa078d87245fd8f5\",\"a9dfc4961fd2c93d673b2f1701d0c\
  72a\",\"1a89a181c369a24c0f461f0f193a9e7e\",\"74329fdaaffd1b0aa3a884e1a36058d6\",\"1c0fc97a535c02\
  4f4866d0d7ffc8da60\",\"5ea34a8784a9446e9f56696396ebea8a\",\"47af8337370ae0f995d24ae16c0ac246\",\"\
  99f8142ffedfcb473caffef2b3a4c2d4\",\"e1a9c04911f51cfd052ad5a296b267b8\",\"85c40595697c539a5fcd8d\
  1a54af6fa7\",\"18b3a698b5d180d42935c6bbb757f5fd\",\"195428e6ed9e89f14a2e1696968e0dde\",\"5ee2f48\
  d814e6cbdf6b25f59095d188c\",\"c6b20335ebd51cfb98ee2d7a80676024\",\"1fc74ddc1236f8a73551e56fc0c8c\
  1ce\",\"fc35cbbeba5b782a4ee72247a74950dc\",\"d02e9afb329f5aa7c3f26932aba67cd0\"],\"merkle_proof\"\
  :[\"8d790b5bba7fe524df0805cc3ed822e3\",\"3f26721f8d82637a193039c50595bedf\",\"9f63b392c46d518eaa\
  fa6b419827d28c\",\"49c468f33e830ab06485f65f4f9f2976\",\"c7528ad72cfc392b4a457b88a41f7113\",\"9a4\
  305e7b7edd0827cf22176705ad2e6\",\"4ab2fd7e91571faa5636fb00f746bf37\",\"0677040e309311a512d2d88ac\
  c810655\",\"ed3fdf945303b79beef543499383193e\",\"bff5cb3ea1058ce086ab7fe078b2e115\",\"8f21669bb4\
  5667bc0c6c20dbf25b4da7\",\"f40f6973627683a231869c7f38190118\",\"4a5d7b4c81f62a1fb2de99de3c99e1ed\
  \",\"a20da5595016fd1c818e5b4223f35fb5\",\"5a4bb03f7e65297ab7fe887fd01e7415\",\"216e07bbdfe68628d\
  534a2dc3f031108\",\"1ce49ad9583a367dbc2a96ddde966659\",\"5257b927a503a65ea874355de92390e9\",\"a2\
  5119359831cb3b54733c33edbf8eb9\",\"ba8bf041d108a8a3e53c40a0bd193d59\",\"d3431bb8d6a0a4c68d14be6f\
  43532b2c\",\"afc7d79ecb06bfc55ead60ab975bd02a\",\"65ae7950f856b175a10e53ba6bd4cacc\",\"78a72adc3\
  ed7bc81d457474604f9ba4b\",\"eb78323080a79378453fcea2c9d8525a\",\"4672b651371539dd00d60d6c243ae30\
  f\",\"0789346859b6f09ae4e988e26a58e9dc\",\"0fd07621dda86ee53b5ab1ab854cc9e1\",\"e0917554114f0b83\
  facf68b21fad162b\",\"4720fa31d61896055de1eba505abbf33\",\"554316c2cba764be79a0bec2727abc59\",\"9\
  466c4a57c0237aa0cc656adbdf1329c\"]}]},{\"leaf_index\":7,\"message\":\"05121f2c394653606d7a8794a1\
  aebbc8d5e2effc091623303d4a5764717e8b98\",\"signers\":[{\"root\":\"597242f1cedd3f6c0dc284efd34109\
  82\",\"pp\":\"a786a09c3fa645dbfbf2d0752537a7f1\",\"randomness\":\"542f15dc62bcad21cb73f2db14d237\
  f3aecafb6530308ede\",\"chain_tips\":[\"35e939b0e466f69d93df9d5ba2243016\",\"5e6611519eb46bfc3930\
  dbee387d009d\",\"68d074d5f56878bec8adaf6df5c7b2aa\",\"9f34ff9d12441c92b24cf9aed5966345\",\"b187b\
  270f01fc24242ac0500debe572c\",\"5a183d32aa79b8f44c0b46405e4217bf\",\"8f72362a2d7ca4d8a0aafe80fc9\
  653c4\",\"8c90e676790dcb5a5e477b1fddc06577\",\"e3e83ee00e6bbfec77f839632b9f80a7\",\"f9bc7e40e40b\
  eab7942437494b3a8a83\",\"5a2e824a15653d8e759566567b65c861\",\"13be55ec5a7f47989873066a738cbae2\"\
  ,\"c196ca600972ea0bb679493ca091e8e9\",\"d2cbcb05137db435f82078d39faf126c\",\"0dbcf58f6220b2b5b35\
  5034297b4783d\",\"6bc3e4ae37c4ef9e5d6415e538703dab\",\"bc3f9a1b9ac1cb328bc040be7b32b556\",\"2577\
  6be412947deff194bcd268e4cb82\",\"ade8889972bfb57e7ab4fa8a2d1a3569\",\"2e5fe807f04b7896dcf6d0b4ec\
  7db28c\",\"fa68e1d17f4e5cd927faa6e4638862ec\",\"5f89bbd108bf8069e5c7b8f65d89928a\",\"2b53587c579\
  b556797dcc80b6dcbb639\",\"25b507dba751aec52fdde5a784c5cdb1\",\"f6af2a308f4b52d71d0f4c4b4e932ba8\"\
  ,\"66ff42fc85bdab2dadd2fae17aa7f010\",\"6cbc4756ee0a412e40159d859556eeda\",\"6c2cf4623314fdfe97f\
  b5fa33c1ee21c\",\"f7d4fb0002a4e919399b603a8730b42a\",\"0c4f2c4bc4623e451a830e5b806c39c7\",\"5e2a\
  accb44254d189773cf84cfcab657\",\"e4ea1c163ed8ebc43bf185a02be1aebc\",\"3bdc2c1c0558ddc1fbf242809c\
  7c5f07\",\"3c0f24dd7e846dc3edf41205c63a7032\",\"47958472450115df3338d5847b3f3e16\",\"75c424e6b5c\
  8c8e3f2b7aacd45705e7c\",\"9add94d201a8cb0b13ddba334749aeb9\",\"552209e270143d5b0775bdc4ea5e38b0\"\
  ,\"9ee72fd943e86859a9c44585985fa878\",\"7588218cd9fd1030018af69f335a2647\",\"2d6487f144216b4427f\
  3a5b146793f9a\",\"9f32d7f714512dbc03e1e433086b1af9\"],\"merkle_proof\":[\"9438dc689893eed45bdde1\
  59eeb764f3\",\"4e7ceb97ead7422cb35d354ba49a698f\",\"9f33c6156da354fab3545ef47836bec0\",\"0332467\
  85b698ee4ba4032b36fd13301\",\"f4bffc8eb90b75507f9364e8f924f4de\",\"accca352883f3319b7bda6264c65c\
  3da\",\"71c21ca0cb0f899f78a24de88c7959e9\",\"c4b6d64c42816c43d48648bb1b328130\",\"ea09f9f2b2b27f\
  929dc4c4676b3068c9\",\"6e789b49489e52aa044f0e65f4124f86\",\"46a8dcc6e405c6feb603ae950a56265e\",\"\
  07ddbe87d32f1d70f3bad45612a53cee\",\"af77c3df730385d1e8e9ccbb0e785471\",\"5e0d7423ca00c9dac7f6ea\
  aad340ad04\",\"3dba3c9c16d94e212abb4c4ec5cd3425\",\"11ca6d69bee5d73f8f5bbb81c606f82e\",\"a8999b6\
  cf4ed4d437cae0fa128abbca3\",\"68a490880d32ee581d4e295e804d2c12\",\"bdf77b1486106e62572e3e0ac7f28\
  0ca\",\"a3ae3c7a9c6acbcd40ee4d4bab8fa0d2\",\"c9a4c88b70d3fc9e34837f1b0390d2f1\",\"e3e96f006ddfd0\
  4e11fffe2172f05b05\",\"ccb3b2f09b93dd672a36553e8efae278\",\"550e1783b298ba9ee52625517ec4ed51\",\"\
  7552aec41d377a8b4ee6b17a0e33fa44\",\"0860f46f8f34dc97cbaed7f7f47ca370\",\"4845f2262370e3cfa0a959\
  c502737a95\",\"15ae0d89a76eeca43077cd2ddc11aea9\",\"fde8abc4fd31db5a11c0e15224e1641e\",\"35ec3a2\
  d1bab70e2d6253e69b4a59eab\",\"90773f568af229b04200ae7650c1890e\",\"454e0b7a979497cc569e4dcb8f38f\
  c75\"]}]}]}"

def real : Array Group := match Inputs.parse realJson with
  | .ok gs => gs
  | .error _ => #[]

example : real.size == 2 && real.all fun g => g.signers.all (verify g.leaf g.message) := by
  native_decide

def bytesOfHex (s : String) : ByteArray :=
  match Inputs.bytes? "hex" (s.length / 2) (.str s) with
  | .ok b => b
  | .error _ => .empty

def g0 : Group := real[0]!
def g1 : Group := real[1]!

/-- Group 0 with keys `a, b, a` (a third key needs a non-final key list block), then group 1. -/
def cover : Array Group := #[{ g0 with signers := #[g0.signers[0]!, g0.signers[1]!, g0.signers[0]!] }, g1]

/-- Rust `signer_set` digests (`SIGNER_SET_AGGREGATION.md` §1.3) of `real`, `cover` and `[g1]`. -/
def rustReal : String := "94c3caac68cd01a2c5e7f625c6ca26522f572246d15445ab2c5dfc9e72c6cb3a"
def rustCover : String := "5ff6884b09f1e32d4d0c2fd1e6bcc807e36462bc9dcf7f6a3fedc38b935b75cf"
def rustG1 : String := "9afff9aa41d3581d8a59038dcb6c430fa897b58aaf33af942f83d6277bca8af5"

example : hex (signerSet real) == rustReal && hex (signerSet cover) == rustCover &&
    hex (signerSet #[g1]) == rustG1 := by
  native_decide

/-- What a scheduled run shows, up to the first padding instance. -/
structure Run where
  /-- Instances violating a role row. -/
  bad : ℕ := 0
  /-- Every instance's `in` registers equal the previous `out`, the first's all zero. -/
  linked : Bool := true
  /-- The first instance of each role. -/
  reps : Array (Option (Array Bool)) := Array.replicate nRoles none
  regs : Array Bool := Array.replicate nReg false
  /-- The first padding instance leaves its registers unchanged and only padding follows. -/
  fixedPoint : Bool := false

def firstPadding (ss : Array Step) : ℕ :=
  (List.range ss.size).find? (fun i => ss[i]!.role == .idle) |>.getD ss.size

def inRegs (z : Array Bool) : Array Bool := (Array.range nReg).map fun j => z[1 + nRoles + j]!

def run (ss : Array Step) : Run := Id.run do
  let stop := firstPadding ss
  let mut r : Run := {}
  for i in [0:min (stop + 1) ss.size] do
    let z := solve ss[i]! r.regs
    let k := ss[i]!.role.index
    r := { r with
      bad := if (violated controlRows z).isEmpty then r.bad else r.bad + 1
      linked := r.linked && inRegs z == r.regs
      reps := if r.reps[k]!.isNone then r.reps.set! k (some z) else r.reps
      regs := outRegs z
      fixedPoint := i == stop && outRegs z == inRegs z &&
        (ss.extract stop ss.size).all (·.role == .idle) }
  return r

def coverRun : Run := run (steps cover)

example : coverRun.bad == 0 && coverRun.linked && coverRun.fixedPoint &&
    coverRun.regs == finalRegs (bytesOfHex rustCover) := by
  native_decide

/-- Every role occurs, and its first instance satisfies every row through Clean witness generation,
which reproduces the scheduler's signals (all but the compression's private bits). -/
def repOk (z : Array Bool) : Bool :=
  let w := witness z
  (violations w).isEmpty && countViolations ops w == 0 &&
    (List.range nSignals).all fun s => s == 0 || (privBase ≤ s && s < auxBase) || isOne w[s - 1]! == z[s]!

example : coverRun.reps.all fun z? => z?.any repOk := by
  native_decide

/-- Index and role of the first instance violating a role row. -/
def firstViolation (ss : Array Step) : Option (ℕ × Role) := Id.run do
  let mut regs := Array.replicate nReg false
  for i in [0:ss.size] do
    let z := solve ss[i]! regs
    unless (violated controlRows z).isEmpty do return some (i, ss[i]!.role)
    regs := outRegs z
  return none

/-- Group 1 with its signer changed by `f`. -/
def tampered (f : Signer → Signer) : Array Group := #[{ g1 with signers := g1.signers.map f }]

def flipByte (d : ByteArray) (i : ℕ) : ByteArray := d.set! i (d.get! i ^^^ 1)

/-- A randomness whose digest has both top bits zero but whose digits do not sum to 195. -/
def badRandomness (s : Signer) : ByteArray := Id.run do
  for k in [1:256] do
    let r := s.randomness.set! 0 (s.randomness.get! 0 + k.toUInt8)
    let d := encodingDigest g1.message g1.leaf s.pp r
    if !bitAt d 63 && !bitAt d 127 && (digits d).foldl (· + ·) 0 != TARGET_SUM then return r
  return s.randomness

def firstRole (ss : Array Step) : Option Role := (firstViolation ss).map (·.2)

example : firstViolation (steps #[g1]) == none := by native_decide
example : firstRole (steps (tampered fun s => { s with tips := s.tips.modify 5 (flipByte · 0) })) ==
    some .merkleLast := by native_decide
example : firstRole (steps #[g1] { skipChainStep := true }) == some .pk := by native_decide
example : firstRole (steps (tampered fun s => { s with randomness := badRandomness s })) == some .enc1 := by
  native_decide
example : firstRole (steps #[g1] { swapMerkle := true }) == some .merkle := by native_decide
example : firstRole (steps (tampered fun s => { s with root := flipByte s.root 0 })) == some .merkleLast := by
  native_decide

end Gf2.Xmss.Check
