//! The designs of a grid of tree shapes, as `checkdesign` compares them with the Lean model of `Design`.

use super::design::{Design, Level};
use super::*;
use crate::rv::Region;
use crate::rv::asm::*;
use std::fmt::Write;

/// The committed summaries, which `checkdesign` reads.
const SUMMARIES: &str = "../../verification/circuits/fixtures/design-summaries.txt";

/// A program of a few instructions, whose shape fixes only the dense polynomials' variables.
fn program() -> Program {
    let text = Asm::new()
        .li(Reg::T0, Region::ADVICE.base())
        .load(Ld, Reg::A0, 0, Reg::T0)
        .exit()
        .finish();
    Program::new(&text, Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
}

/// A design as `checkdesign` reads it: its places, tiers, kinds, unions, variables and statement.
fn summary(d: &Design<'_>) -> String {
    let mut s = String::new();
    let places: Vec<String> = (d.places.iter())
        .map(|p| match p.level {
            Level::First => format!("{}:F", p.tier),
            Level::Node(a) => format!("{}:N:{a}", p.tier),
            Level::Wrap => format!("{}:W", p.tier),
        })
        .collect();
    let _ = writeln!(s, "places {}", places.join(" "));
    let tiers: Vec<String> = (d.tiers.iter())
        .map(|t| format!("{}-{}", t.places.start, t.places.end))
        .collect();
    let _ = writeln!(s, "tiers {}", tiers.join(" "));
    let codes: Vec<String> = (0..d.places.len()).map(|p| d.code(p).to_string()).collect();
    let _ = writeln!(s, "codes {}", codes.join(" "));
    let positions: Vec<String> = (0..40)
        .map(|c| d.position(c).map_or_else(|| "-".to_owned(), |p| p.to_string()))
        .collect();
    let _ = writeln!(s, "positions {}", positions.join(" "));
    let unions: Vec<String> = (0..d.places.len())
        .map(|p| {
            d.union_shape(p).map_or_else(
                || "-".to_owned(),
                |u| {
                    format!(
                        "{}:{}:{}:{}",
                        u.arity,
                        u.children.chunks,
                        u.declared.chunks,
                        u8::from(u.optional)
                    )
                },
            )
        })
        .collect();
    let _ = writeln!(s, "unions {}", unions.join(" "));
    let [v0, v1, v2, v3] = d.vars.0;
    let _ = writeln!(s, "vars {v0} {v1} {v2} {v3}");
    let kappas: Vec<String> = d.tiers.iter().map(|t| t.fixed.kappa().to_string()).collect();
    let _ = writeln!(s, "kappas {}", kappas.join(" "));
    let _ = writeln!(s, "statement {} {}", d.statement.len(), d.statement.polys().len());
    s
}

/// The grid's shapes: arities around the edges Tree::new checks, and claim-set trees of one tier and of two whose
/// small tier is within, at, and past the tree's.
fn grid() -> Vec<(usize, usize, Option<ClaimShape>)> {
    let cap = |claims, groups| Capacity { claims, groups };
    let mut shapes = Vec::new();
    for arity_0 in [0, 1, 2, 3, 5] {
        for arity in [0, 1, 2, 3, 4, 7] {
            shapes.push((arity_0, arity, None));
            for large in [cap(1, 1), cap(12, 4), cap(100, 9)] {
                shapes.push((arity_0, arity, Some(ClaimShape::new(large))));
            }
            let large = cap(12, 4);
            for small_arity in [1, 2, 3, arity, arity + 1] {
                for capacity in [cap(5, 2), cap(12, 4), cap(13, 4), cap(12, 5)] {
                    let small = Some(Tier {
                        arity: small_arity,
                        capacity,
                    });
                    let shape = (arity_0, arity, Some(ClaimShape { capacity: large, small }));
                    if !shapes.contains(&shape) {
                        shapes.push(shape);
                    }
                }
            }
        }
    }
    shapes
}

/// Every grid shape: whether `Tree::new` refuses its arities or small tier, and if not, its design.
fn summaries() -> String {
    let program = program();
    let rate = Rate::MIN;
    let measured = LeafShape::measured(&program.measure(&[1]).expect("the run halts"), rate);
    // A leaf shape no proof has, so that `Tree::new` stops at the leaf's shape once the arities pass.
    let refused = LeafShape::new(measured.taus.map(|_| 99), rate);
    let mut out = format!(
        "consts {} {}\n",
        crate::class_flock::FlockId::MAX_K_LOG,
        crate::class_flock::N_FLOCKS
    );
    for (arity_0, arity, claims) in grid() {
        let claim_words = match claims {
            None => "none".to_owned(),
            Some(c) => {
                let large = format!("{} {}", c.capacity.claims, c.capacity.groups);
                match c.small {
                    None => format!("{large} -"),
                    Some(s) => format!("{large} {} {} {}", s.arity, s.capacity.claims, s.capacity.groups),
                }
            }
        };
        let _ = writeln!(out, "shape {arity_0} {arity} {claim_words}");
        let shape = TreeShape {
            leaf: refused,
            arity_0,
            arity,
            rate,
            claims,
        };
        match Tree::new(&program, shape) {
            Err(TreeError::Arity { .. }) => out.push_str("reject arity\n"),
            Err(TreeError::SmallTier { .. }) => out.push_str("reject small\n"),
            Err(TreeError::LeafShape(_)) => {
                out.push_str("accept\n");
                let leaf = ProofShape::new(&program, measured.taus, rate).expect("the measured shape");
                let tiers = claims.map_or(1, |c| c.tiers());
                let taus = vec![PerRecTable::default(); tiers];
                let d = Design::new(leaf, arity_0, arity, rate, claims, &taus).expect("a design at zero heights");
                out.push_str(&summary(&d));
            }
            Err(e) => panic!("shape {arity_0} {arity} {claims:?}: {e}"),
            Ok(_) => panic!("a tree of a leaf shape no proof has"),
        }
        out.push_str("end\n");
    }
    out
}

/// The committed summaries are the designs: `LEANVM_BLESS=1` rewrites them.
#[test]
fn the_design_summaries_are_the_designs() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(SUMMARIES);
    let built = summaries();
    if std::env::var_os("LEANVM_BLESS").is_some() {
        std::fs::write(&path, &built).expect("the fixture is writable");
    }
    let committed = std::fs::read_to_string(&path).expect("the committed summaries");
    assert!(committed == built, "the design summaries changed: rerun with LEANVM_BLESS=1");
}
