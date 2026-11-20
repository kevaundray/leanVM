//! The guest's advice: the run of `guests/ml_dsa.py` replayed on integers, each hint stream in the order the guest
//! pops it.

use verifier::E;

use crate::fips::{self, D, Params, Q};
use crate::{Claim, Rejected, Streams};

/// `g^v` for an integer `v` the exponent holds, `v` taken mod `2^64 - 1` (a negative `v` wraps, and no range check
/// passes it).
fn g(v: i128) -> E {
    E::new(2, 0).pow(v.rem_euclid((1 << 64) - 1) as u64)
}

fn lane(bytes: &[u8]) -> E {
    E::new(u64::from_le_bytes(bytes.try_into().unwrap()), 0)
}

/// The hint streams as they fill.
#[derive(Default)]
struct Builder(Streams);

impl Builder {
    fn push(&mut self, name: &str, entry: Vec<E>) {
        match self.0.iter_mut().find(|(n, _)| n == name) {
            Some((_, entries)) => entries.push(entry),
            None => self.0.push((name.to_string(), vec![entry])),
        }
    }

    /// A twiddle product as `tw_mul` takes it: `b = r + q u` with `r` in 6-bit digits (the last below 32), `u`
    /// hinted when `wq`, and returns `t = sum_k (zeta 64^k j_k mod q)`, `t = zeta b (mod q)`.
    fn tw(&mut self, b: i128, zeta: i128, wq: bool) -> i128 {
        let q = Q as i128;
        let (r, u) = (b.rem_euclid(q), b.div_euclid(q));
        assert!(b >= 0 && u < if wq { 1024 } else { 1 }, "a twiddle product's input {b} is past its digits");
        let d: [i128; 4] = std::array::from_fn(|k| r >> (6 * k) & 63);
        let entry = d.iter().chain(wq.then_some(&u)).map(|&v| g(v)).collect();
        self.push("tw", entry);
        (0..4).map(|k| (zeta << (6 * k)) * d[k] % q).sum()
    }
}

/// The UseHint columns: for each index `k' = r1 + (m + 1) s + (2m + 1) h`, `r1 2 gamma2 + s gamma2`, `h` and
/// UseHint's result, where `s` says `r0 > 0`.
pub fn use_hint_columns(p: &Params) -> [Vec<u64>; 3] {
    let m = p.m();
    let (mut d, mut h, mut w1) = (vec![], vec![], vec![]);
    for kp in 0..4 * m + 2 {
        let (hb, k) = (kp / (2 * m + 1), kp % (2 * m + 1));
        let (s, r1) = (k / (m + 1), k % (m + 1));
        d.push(r1 * 2 * p.gamma2 + s * p.gamma2);
        h.push(hb);
        w1.push(match (hb, s) {
            (0, _) => r1 % m,
            (_, 1) => (r1 + 1) % m,
            _ => (r1 + m - 1) % m,
        });
    }
    [d, h, w1]
}

/// The streams of the claims in order, or why the guest cannot accept one.
pub fn streams(p: &Params, claims: &[Claim]) -> Result<Streams, Rejected> {
    let mut s = Builder::default();
    for claim in claims {
        claim_streams(p, claim, &mut s)?;
    }
    Ok(s.0)
}

fn claim_streams(p: &Params, claim: &Claim, s: &mut Builder) -> Result<(), Rejected> {
    let pk = fips::decode_pk(p, &claim.pk).ok_or(Rejected::MalformedKey)?;
    let sig = fips::decode_sig(p, &claim.sig).ok_or(Rejected::MalformedSignature)?;
    let (k, l, tau) = (p.k, p.l, p.tau);

    s.push("rho", claim.pk[..32].chunks(8).map(lane).collect());
    for i in 0..k {
        for u in 0..8 {
            let bytes = &claim.pk[32 + 320 * i + 40 * u..][..40];
            s.push("t1", bytes.iter().map(|&b| g(b.into())).collect());
        }
    }
    s.push("mu", claim.mu.chunks(8).map(lane).collect());

    // ExpandA: five SHAKE128 blocks a polynomial, the accepted candidates' values.
    let mut a_hat = vec![vec![[0i128; 256]; l]; k];
    for (i, row) in a_hat.iter_mut().enumerate() {
        for (j, poly) in row.iter_mut().enumerate() {
            let mut seed = pk.rho.to_vec();
            seed.extend([j as u8, i as u8]);
            let bytes = fips::shake(168, &seed, 5 * 168);
            let mut n = 0;
            for block in bytes.chunks(168) {
                s.push("exa", block.iter().map(|&b| g(b.into())).collect());
                for c in block.chunks(3) {
                    let v = u64::from(c[0]) | u64::from(c[1]) << 8 | u64::from(c[2] & 127) << 16;
                    if c[2] & 127 == 127 {
                        s.push("exr", vec![E::new(u64::from(v >= Q), 0)]);
                    }
                    if v < Q {
                        if n < 256 {
                            poly[n] = v.into();
                        }
                        n += 1;
                    }
                }
            }
            if n < 256 {
                return Err(Rejected::Unsupported("ExpandA needs a sixth block"));
            }
        }
    }

    // SampleInBall: one SHAKE256 block, its first lane the signs.
    s.push("ct", sig.ctilde.chunks(8).map(lane).collect());
    let block = fips::shake256(&sig.ctilde, 136);
    s.push("sib", block.iter().map(|&b| g(b.into())).collect());
    let signs = u64::from_le_bytes(block[..8].try_into().unwrap());
    let mut js = vec![];
    for &j in &block[8..] {
        if js.len() == tau {
            break;
        }
        let i = 256 - tau + js.len();
        let accept = usize::from(j) <= i;
        s.push("sibf", vec![E::new(u64::from(!accept), 0)]);
        if accept {
            js.push(usize::from(j));
        }
    }
    if js.len() < tau {
        return Err(Rejected::Unsupported("SampleInBall needs a second block"));
    }
    let mut c = [0i128; 256];
    for (kk, &j) in js.iter().enumerate() {
        let i = 256 - tau + kk;
        c[i] = c[j];
        c[j] = if signs >> kk & 1 == 1 { -1 } else { 1 };
    }

    // f NTT(z), f = 512^-1 mod q, from z + ZB, each butterfly's product by `tw`; layer 0 multiplies both inputs.
    let zetas: Vec<i128> = fips::zetas().iter().map(|&z| i128::from(z)).collect();
    let (q, zb) = (Q as i128, p.z_bound() as i128);
    let f = 8364049;
    assert_eq!(512 * f % q, 1);
    let fz = f * zetas[1] % q;
    let (kf, kfz) = (f * zb % q, fz * zb % q);
    let mut z_hat = vec![[0i128; 256]; l];
    for (j, zj) in sig.z.iter().enumerate() {
        let zz: Vec<i128> = zj.iter().map(|&z| i128::from(z) + zb).collect();
        s.push("z", zz.iter().map(|&z| g(z)).collect());
        let mut w = [0i128; 256];
        for n in 0..128 {
            let a = s.tw(zz[n], f, false);
            let t = s.tw(zz[n + 128], fz, false);
            w[n] = a + t + 2 * q - kf - kfz;
            w[n + 128] = a + 5 * q - kf + kfz - t;
        }
        for lay in 1..8 {
            let len = 128 >> lay;
            let mut nw = [0i128; 256];
            for blk in 0..1 << lay {
                for jj in 0..len {
                    let st = 2 * len * blk + jj;
                    let a = w[st];
                    let t = s.tw(w[st + len], zetas[(1 << lay) + blk], true);
                    nw[st] = a + t;
                    nw[st + len] = a + 4 * q - t;
                }
            }
            w = nw;
        }
        for (m, &x) in w.iter().enumerate() {
            let (r, u) = (x.rem_euclid(q), x.div_euclid(q));
            s.push("zr", vec![g(r & 4095), g(r >> 12), g(u)]);
            z_hat[j][m] = r;
        }
    }

    // 2 A NTT(z), as the guest sums it over limbs, then reduced.
    let mut w_hat = vec![[0i128; 256]; k];
    for m in 0..256 {
        for i in 0..k {
            let x = 2 * (0..l).map(|j| a_hat[i][j][m] * z_hat[j][m]).sum::<i128>();
            let (r, t) = (x.rem_euclid(q), x.div_euclid(q));
            s.push("wr", vec![g(r & 4095), g(r >> 12), g(t & 511), g(t >> 9 & 511), g(t >> 18)]);
            w_hat[i][m] = r;
        }
    }

    // NTT^-1 without its factor 256^-1, each difference lifted past the values entering its layer.
    let mut o = vec![[0i128; 256]; k];
    for i in 0..k {
        let mut w = w_hat[i];
        for lay in 0..8 {
            let len = 1 << lay;
            let mut nw = [0i128; 256];
            for blk in 0..128 >> lay {
                for jj in 0..len {
                    let st = 2 * len * blk + jj;
                    let (a, b) = (w[st], w[st + len]);
                    nw[st] = a + b;
                    nw[st + len] = s.tw(b + (q << (lay + 1)) - a, zetas[(256 >> lay) - 1 - blk], true);
                }
            }
            w = nw;
        }
        o[i] = w;
    }

    // w' = o - c t1 2^d, UseHint, the hint bits counted.
    let m_w1 = p.m() as i128;
    let gamma2 = p.gamma2 as i128;
    for i in 0..k {
        let ct1: [i128; 256] = std::array::from_fn(|m| {
            (0..256)
                .map(|n| {
                    let t = i128::from(pk.t1[i][(m + 256 - n) % 256]);
                    if n <= m { c[n] * t } else { -c[n] * t }
                })
                .sum()
        });
        for m in 0..256 {
            let x = o[i][m] - (ct1[m] << D) + 64 * q;
            assert!((0..512 * q).contains(&o[i][m]) && x >= 0);
            let rr = x.rem_euclid(Q as i128);
            // Decompose, the r1 = m case kept as r1 = m, r0 <= 0.
            let mut r0 = rr.rem_euclid(2 * gamma2);
            if r0 > gamma2 {
                r0 -= 2 * gamma2;
            }
            let r1 = (rr - r0) / (2 * gamma2);
            let sb = i128::from(r0 > 0);
            let h = i128::from(sig.h[i][m]);
            let kp = r1 + (m_w1 + 1) * sb + (2 * m_w1 + 1) * h;
            let u = r0 + gamma2 - 1 - sb * gamma2;
            let t = (x + gamma2 - 1 - (r1 * 2 * gamma2 + sb * gamma2) - u) / q;
            assert_eq!(x + gamma2 - 1, r1 * 2 * gamma2 + sb * gamma2 + u + t * q);
            assert!((0..1024).contains(&t));
            s.push("fin", vec![g(kp), g(u), g(t)]);
        }
    }
    Ok(())
}
