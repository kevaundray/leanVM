from __future__ import annotations

import hashlib
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from functools import cache, reduce
from itertools import accumulate, islice, repeat
from operator import mul
from pathlib import Path
from struct import pack, unpack


class VerificationError(Exception):
    """Invalid proof."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


# Field arithmetic ------------------------------------------------------------


def _base_mul(left: int, right: int) -> int:
    product = 0
    while right:
        if right & 1:
            product ^= left
        right >>= 1
        left <<= 1
    low, high = product & (2**64 - 1), product >> 64
    folded = low ^ high ^ (high << 1) ^ (high << 3) ^ (high << 4)
    overflow = folded >> 64
    return ((folded & (2**64 - 1)) ^ overflow ^ (overflow << 1) ^ (overflow << 3) ^ (overflow << 4)) & (2**64 - 1)


@dataclass(frozen=True, slots=True)
class K:
    """GF(2^64) = F2[x]/(x^64 + x^4 + x^3 + x + 1)"""

    value: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.value, int) or isinstance(self.value, bool) or not 0 <= self.value <= (2**64 - 1):
            raise ValueError("a K element is a 64-bit unsigned integer")

    def __index__(self) -> int:
        return self.value

    def to_bytes(self) -> bytes:
        """Its transport image: one 64-bit little-endian word."""
        return self.value.to_bytes(8, "little")

    def __bool__(self) -> bool:
        return bool(self.value)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, K):
            return self.value == other.value
        return isinstance(other, int) and not isinstance(other, bool) and self.value == other

    def __hash__(self) -> int:
        return hash(self.value)

    def __add__(self, other: object) -> K:
        rhs = _as_k(other)
        return NotImplemented if rhs is None else K(self.value ^ rhs.value)

    __radd__ = __add__

    def __mul__(self, other: object) -> K:
        rhs = _as_k(other)
        return NotImplemented if rhs is None else K(_base_mul(self.value, rhs.value))

    __rmul__ = __mul__

    def __repr__(self) -> str:
        return f"K(0x{self.value:016x})"


def _as_k(value: object) -> K | None:
    if isinstance(value, K):
        return value
    if isinstance(value, int) and not isinstance(value, bool) and 0 <= value <= 2**64 - 1:
        return K(value)
    return None


@dataclass(frozen=True, slots=True, init=False)
class E:
    """K[y]/(y^3 + y + 1): the challenge field, a degree-3 extension of K. Limbs may be given as plain integers, which are lifted."""

    c0: K
    c1: K
    c2: K

    def __init__(self, c0: K | int = 0, c1: K | int = 0, c2: K | int = 0) -> None:
        object.__setattr__(self, "c0", c0 if isinstance(c0, K) else K(c0))
        object.__setattr__(self, "c1", c1 if isinstance(c1, K) else K(c1))
        object.__setattr__(self, "c2", c2 if isinstance(c2, K) else K(c2))

    @classmethod
    def from_bytes(cls, data: bytes) -> E:
        require(len(data) == 24, "a field element must contain exactly 24 bytes")
        return cls(*unpack("<3Q", data))

    def to_bytes(self) -> bytes:
        return pack("<3Q", self.c0, self.c1, self.c2)

    @staticmethod
    def lift(value: object) -> E:
        """`value` as an extension element; anything that is not one is an error."""
        if isinstance(value, E):
            return value
        lifted = _as_k(value)
        if lifted is not None:
            return E(lifted)
        raise TypeError(f"cannot use {type(value).__name__} as a field element")

    @staticmethod
    def sum(values: Iterable[E]) -> E:
        return sum(values, ZERO)

    def __int__(self) -> int:
        return self.c0.value | self.c1.value << 64 | self.c2.value << 128

    def __bool__(self) -> bool:
        return bool(self.c0 or self.c1 or self.c2)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, E):
            return self.c0 == other.c0 and self.c1 == other.c1 and self.c2 == other.c2
        return not (self.c1 or self.c2) and self.c0 == other

    def __hash__(self) -> int:
        return hash(int(self))

    def __add__(self, other: object) -> E:
        rhs = self.lift(other)
        return E(self.c0 + rhs.c0, self.c1 + rhs.c1, self.c2 + rhs.c2)

    __radd__ = __add__

    def __mul__(self, other: object) -> E:
        rhs = self.lift(other)
        # y^3 = y + 1 folds the degree-4 product back into three limbs.
        p0 = self.c0 * rhs.c0
        p1 = self.c0 * rhs.c1 + self.c1 * rhs.c0
        p2 = self.c0 * rhs.c2 + self.c1 * rhs.c1 + self.c2 * rhs.c0
        p3 = self.c1 * rhs.c2 + self.c2 * rhs.c1
        p4 = self.c2 * rhs.c2
        return E(p0 + p3, p1 + p3 + p4, p2 + p4)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> E:
        if exponent < 0:
            return self.inv() ** -exponent
        base, out, n = self, ONE, exponent
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n >>= 1
        return out

    def inv(self) -> E:
        require(bool(self), "division by zero in GF(2^192)")
        return self ** (2**192 - 2)

    def __truediv__(self, other: object) -> E:
        rhs = self.lift(other)
        return self * rhs.inv()

    def __repr__(self) -> str:
        return f"E(0x{self.c2.value:016x}{self.c1.value:016x}{self.c0.value:016x})"


ZERO = E(0)
ONE = E(1)
GEN = E(2)
Y = E(0, 1)  # the tower generator, y^3 = y + 1


def powers(base: E, count: int) -> list[E]:
    """`[1, base, base^2, ...]`, `count` terms."""
    return list(islice(accumulate(repeat(base), mul, initial=ONE), count))


# BLAKE2s and digests ---------------------------------------------------------

BLAKE2S_IV = (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19)  # fmt: skip
BLAKE2S_SIGMA = ((0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15), (14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3), (11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4), (7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8), (9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13), (2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9), (12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11), (13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10), (6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5), (10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0))  # fmt: skip
BLAKE2S_G_LANES = ((0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15), (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14))  # fmt: skip


def blake2s_hash(data: bytes) -> Digest:
    """Standard 32-byte unkeyed BLAKE2s-256 hash."""
    return Digest(hashlib.blake2s(data).digest())


@dataclass(frozen=True, slots=True)
class Digest:
    """256 bits"""

    value: bytes

    def __post_init__(self) -> None:
        require(len(self.value) == 32, "a digest is 256 bits")

    def words(self) -> tuple[int, int, int, int]:
        """Its four 64-bit words, the form the compression chain runs in."""
        return unpack("<4Q", self.value)

    def halves(self) -> tuple[E, E]:
        """Its two 128-bit halves, the one form a digest travels in."""
        w0, w1, w2, w3 = self.words()
        return (E(w0, w1), E(w2, w3))

    @classmethod
    def from_halves(cls, low: E, high: E) -> Digest:
        require(not (low.c2 or high.c2), "a digest half is 128-bit")
        return cls(pack("<4Q", low.c0, low.c1, high.c0, high.c1))


# Multilinear and stacking helpers --------------------------------------------


type MultilinearPoint = tuple[E, ...]


def eq_kernel(point: Sequence[E]) -> list[E]:
    out = [ONE]
    for r in point:
        out = [v * (ONE + r) for v in out] + [v * r for v in out]
    return out


def multilinear_eval(mle: Sequence[K | E], point: Sequence[E]) -> E:
    require(len(mle) == 2 ** len(point), "multilinear table has the wrong size")
    cur = [E.lift(value) for value in mle]
    for r in point:
        cur = [cur[2 * i] * (ONE + r) + cur[2 * i + 1] * r for i in range(len(cur) // 2)]
    return cur[0]


def log2_ceil(value: int) -> int:
    return (max(1, value) - 1).bit_length()


def log2_strict(value: int) -> int:
    require(value > 0 and not value & (value - 1), "expected a power of two")
    return value.bit_length() - 1


def eq_eval(left: Sequence[E], right: Sequence[E]) -> E:
    result = ONE
    for x, y in zip(left, right, strict=True):
        result *= ONE + x + y
    return result


def dot(left: Sequence[K | E], right: Sequence[K | E]) -> E:
    result = ZERO
    for x, y in zip(left, right, strict=True):
        result += E.lift(x) * y
    return result


def index_mle(point: MultilinearPoint) -> E:
    """MLE of ``[1, g, g^2, ...]`` at an LSB-first point."""
    result = ONE
    generator_power = GEN
    for challenge in point:
        result *= ONE + challenge * (ONE + generator_power)
        generator_power **= 2
    return result


def poly_eval(coefficients: Sequence[E], point: E) -> E:
    """A polynomial at `point`, by Horner over its coefficients, constant first."""
    return reduce(lambda acc, c: acc * point + c, reversed(coefficients), ZERO)


@dataclass(frozen=True)
class Placement:
    """Where something sits in the stacked cube: a claim's point fills the `variables` coordinates above `low`, the bits of `index` fixing the rest.
    `low` is zero for a block with a cube of its own, and the slot width for a column interleaved into a bigger block."""

    variables: int
    index: int
    low: int = 0

    def stack_point(self, point: MultilinearPoint, stack_log: int) -> MultilinearPoint:
        bits = _selector_point(self.index, stack_log)
        return bits[: self.low] + tuple(point) + bits[self.low + self.variables :]

    def eq_above(self, point: Sequence[E]) -> E:
        """eq weight of the coordinates above the window."""
        bits = _selector_point(self.index >> (self.low + self.variables), len(point) - self.low - self.variables)
        return eq_eval(bits, point[self.low + self.variables :])


def stack_offsets(sizes: Sequence[int]) -> tuple[list[int], int]:
    offsets = [0] * len(sizes)
    total = 0
    for index, size in sorted(enumerate(sizes), key=lambda item: (-item[1], item[0])):
        offsets[index] = total
        total += 2**size
    return offsets, log2_ceil(total)


def _selector_point(selector: int, length: int) -> MultilinearPoint:
    return tuple(E(selector >> bit & 1) for bit in range(length))


# Canonical native proof transport -------------------------------------------

MAX_ELEMENTS = 1 << 24


@dataclass(frozen=True)
class Opening:
    leaf: tuple[int, ...]
    siblings: tuple[bytes, ...]


@dataclass(frozen=True)
class Proof:
    stream: tuple[E, ...]
    merkle_openings: tuple[Opening, ...]

    @classmethod
    def load(cls, source: Path | bytes) -> Proof:
        data = source.read_bytes() if isinstance(source, Path) else source
        offset = 0

        def take(n: int) -> bytes:
            nonlocal offset
            require(0 <= n <= len(data) - offset, "truncated proof")
            result = data[offset : offset + n]
            offset += n
            return result

        def length(item_size: int) -> int:
            n = int.from_bytes(take(8), "little")
            require(n <= MAX_ELEMENTS and n <= (len(data) - offset) // item_size, "invalid proof length")
            return n

        require(take(8) == b"RV64PRF1", "invalid native proof magic")
        stream = tuple(E.from_bytes(take(24)) for _ in range(length(24)))
        openings = []
        for _ in range(length(16)):
            count = length(8)
            require(count <= 64, "too many leaf words")
            leaf = tuple(int.from_bytes(take(8), "little") for _ in range(count))
            count = length(32)
            require(count <= 32, "too many Merkle siblings")
            openings.append(Opening(leaf, tuple(take(32) for _ in range(count))))
        require(offset == len(data), "trailing proof bytes")
        return cls(stream, tuple(openings))


# Fiat--Shamir ---------------------------------------------------------------

DS_OBSERVE = 1
DS_SQUEEZE = 2
DS_POW_BASE = 3
DS_POW_NONCE = 4


def compress(left: Sequence[K | int], right: Sequence[K | int]) -> tuple[int, int, int, int]:
    """Hash two four-word operands, a word being a plain integer or the K element standing for it."""
    return unpack("<4Q", blake2s_hash(b"".join(int(x).to_bytes(8, "little") for x in (*left, *right))).value)


class Transcript:
    def __init__(self, proof: Proof, fiat_shamir_IV: Digest, public_input: Digest) -> None:
        self.proof = proof
        self.state = compress(fiat_shamir_IV.words(), public_input.words())
        self.stream_offset = 0  # in E field elements
        self.opening_offset = 0  # in bytes

    def observe(self, value: E) -> None:
        self.state = compress(self.state, (value.c0, value.c1, value.c2, DS_OBSERVE))

    def sample(self) -> E:
        self.state = compress(self.state, (0, 0, 0, DS_SQUEEZE))
        return E(*self.state[:3])

    def samples(self, count: int) -> list[E]:
        return [self.sample() for _ in range(count)]

    def _next(self) -> E:
        require(self.stream_offset < len(self.proof.stream), "proof stream exhausted")
        value = self.proof.stream[self.stream_offset]
        self.stream_offset += 1
        return value

    def next_scalar(self) -> E:
        value = self._next()
        self.observe(value)
        return value

    def next_scalars(self, count: int) -> list[E]:
        return [self.next_scalar() for _ in range(count)]

    def grind_check(self, bits: int) -> None:
        nonce = self._next()
        block = (nonce.c0, nonce.c1, nonce.c2, DS_POW_NONCE)
        digest = compress(compress(self.state, (0, 0, 0, DS_POW_BASE)), block)[0]
        valid = nonce == ZERO if bits == 0 else digest & (2**bits - 1) == 0
        self.state = compress(self.state, block)
        require(valid, "invalid grinding nonce")

    def merkle(self, root: Digest, block_length: int, queries: Sequence[int], leaf_words: int) -> list[tuple[K, ...]]:
        height = log2_strict(block_length)
        require(leaf_words <= MAX_ELEMENTS, "invalid leaf size")
        require(len(queries) <= len(self.proof.merkle_openings) - self.opening_offset, "Merkle opening missing")
        rows = []
        for query in queries:
            require(0 <= query < block_length, "Merkle query outside tree")
            opening = self.proof.merkle_openings[self.opening_offset]
            self.opening_offset += 1
            require(len(opening.leaf) == leaf_words and len(opening.siblings) == height, "invalid Merkle opening shape")
            node = blake2s_hash(b"".join(word.to_bytes(8, "little") for word in opening.leaf))
            for level, sibling in enumerate(opening.siblings):
                left, right = (node.value, sibling) if query >> level & 1 == 0 else (sibling, node.value)
                node = blake2s_hash(left + right)
            require(node == root, "Merkle root mismatch")
            rows.append(tuple(K(word) for word in opening.leaf))
        return rows

    def sumcheck_round_poly(self, count: int, claim: E, eq_factor: E | None = None) -> list[E]:
        """returns q(X) := c0 + c1X + c2X^2 + ..."""
        if eq_factor is None:
            constant, tail = self.next_scalar(), self.next_scalars(count - 2)  # `q(0) + q(1) == claim`. The transcript contains c0, c2, c3 ...
            return [constant, claim + E.sum(tail), *tail]
        # `(1 + r) q(0) + r q(1) == claim`. The transcript contains c1, c2, c3 ... (r := eq_factor)
        tail = self.next_scalars(count - 1)
        return [claim + eq_factor * E.sum(tail), *tail]

    def finish(self) -> None:
        require(self.stream_offset == len(self.proof.stream), "proof stream not fully consumed")
        require(self.opening_offset == len(self.proof.merkle_openings), "Merkle openings not fully consumed")


def sumcheck(transcript: Transcript, claim: E, count: int, equalities: Sequence[E | None]) -> tuple[MultilinearPoint, E]:
    point = []
    for equality in equalities:
        message = transcript.sumcheck_round_poly(count, claim, equality)
        challenge = transcript.sample()
        point.append(challenge)
        claim = poly_eval(message, challenge)
    return tuple(point), claim


# Bus balance and decomposition ---------------------------------------------


def verify_gkr_grand_products(depth: int, transcript: Transcript) -> tuple[E, MultilinearPoint, tuple[E, E, E]]:
    shared, count = transcript.next_scalar(), transcript.next_scalar()
    combiner = transcript.sample()
    point: list[E] = []
    values = (shared, shared, count)  # 3 grand product GKR are batched together: push, pull, count

    layer = depth
    while layer > 0:
        # Two levels a step. An odd depth starts with one.
        step = 1 if layer % 2 else 2
        claim = poly_eval(values, combiner)
        # The product is degree 2^step, so one more coefficient than that per round.
        x, claim = sumcheck(transcript, claim, 2**step + 1, point)

        children = [transcript.next_scalars(2**step) for _ in range(3)]
        products = [reduce(mul, child) for child in children]
        require(claim == poly_eval(products, combiner), f"GKR layer {layer}: children do not match the sumcheck")

        y = transcript.samples(step)
        values = [multilinear_eval(child, y) for child in children]
        combiner = transcript.sample()
        point = [*y, *x]
        layer -= step

    return count, tuple(point), (values[0], values[1], values[2])


@dataclass
class Form:
    """A polynomial of degree at most 2 in a table's columns."""

    terms: dict[tuple[int, ...], E] = field(default_factory=dict)  # monomial -> coefficient; () is 1, (i,) is x_i, (i, j) is x_i*x_j

    def add_scaled(self, other: Form, weight: E) -> None:
        for monomial, coefficient in other.terms.items():
            self.terms[monomial] = self.terms.get(monomial, ZERO) + weight * coefficient

    def __add__(self, other: Form) -> Form:
        combined = Form(dict(self.terms))
        combined.add_scaled(other, ONE)
        return combined

    @staticmethod
    def sum(forms: Iterable[Form]) -> Form:
        """`Σ forms`, the empty sum being the zero polynomial."""
        return sum(forms, Form())

    def evaluate(self, column: Callable[[int], E]) -> E:
        return E.sum(reduce(mul, map(column, monomial), c) for monomial, c in self.terms.items())


# Public ELF statement --------------------------------------------------------

R1CS_DIGEST = bytes.fromhex("537ad20790308f8eb8c0e8bd3e6c58ee64573371e3d53c30613dd04d87c0b7ea")
RAM_END = 1 << 32


@dataclass(frozen=True)
class Segment:
    address: int
    memory_size: int
    flags: int
    data: bytes


@dataclass(frozen=True)
class ProgramInfo:
    entry: int
    segments: tuple[Segment, ...]
    digest: Digest

    @classmethod
    def from_elf(cls, elf: bytes) -> ProgramInfo:
        require(len(elf) >= 64 and elf[:7] == b"\x7fELF\x02\x01\x01", "expected ELF64LE version 1")

        def number(at: int, size: int) -> int:
            return int.from_bytes(elf[at : at + size], "little")

        entry = number(24, 8)
        require(number(16, 2) == 2 and number(18, 2) == 243 and number(20, 4) == 1, "expected RISC-V ET_EXEC")
        require(
            number(48, 4) == 0 and number(52, 2) == 64 and number(54, 2) == 56 and entry & 3 == 0,
            "invalid ELF flags, header sizes, or entry alignment",
        )
        phoff, phnum = number(32, 8), number(56, 2)
        require(0 < phnum < 0xFFFF and phoff >= 64 and phoff + phnum * 56 <= len(elf), "invalid program headers")
        segments = []
        for index in range(phnum):
            p = phoff + index * 56
            kind = number(p, 4)
            require(kind not in (2, 3), "dynamic ELF is unsupported")
            if kind != 1:
                continue
            flags, offset, address = number(p + 4, 4), number(p + 8, 8), number(p + 16, 8)
            filesz, memsz, alignment = number(p + 32, 8), number(p + 40, 8), number(p + 48, 8)
            require(flags & ~7 == 0 and flags & 3 != 3 and filesz <= memsz, "invalid segment permissions or size")
            require(offset + filesz <= len(elf) and address < RAM_END and address + memsz <= RAM_END, "segment outside ELF or RAM")
            require(alignment <= 1 or (alignment & (alignment - 1) == 0 and address % alignment == offset % alignment), "invalid segment alignment")
            segments.append(Segment(address, memsz, flags, elf[offset : offset + filesz]))
        segments.sort(key=lambda s: s.address)
        previous_end = 0
        for segment in segments:
            if segment.memory_size:
                require(segment.address >= previous_end, "overlapping PT_LOAD ranges")
                previous_end = segment.address + segment.memory_size
        require(
            all(any(s.flags & 1 and s.address <= entry + i < s.address + s.memory_size for s in segments) for i in range(4)),
            "entry is not executable mapped memory",
        )
        return cls(entry, tuple(segments), blake2s_hash(elf))

    def rom_entries(self) -> list[tuple[int, int]]:
        entries = {(segment.address + i) << 1: byte for segment in self.segments for i, byte in enumerate(segment.data)}
        candidates = {
            pc
            for segment in self.segments
            if segment.flags & 1 and segment.data
            for pc in range(segment.address & ~3, segment.address + len(segment.data), 4)
        }
        for pc in candidates:
            word = 0
            for i in range(4):
                address = pc + i
                segment = next((s for s in self.segments if s.address <= address < s.address + s.memory_size), None)
                if segment is None or not segment.flags & 1:
                    break
                offset = address - segment.address
                byte = segment.data[offset] if offset < len(segment.data) else 0
                word |= byte << (8 * i)
            else:
                entries[(pc << 1) | 1] = word
        return sorted(entries.items())

    def iv(self) -> Digest:
        return blake2s_hash(b"leanvm/rv64im/proof/v1" + self.digest.value + R1CS_DIGEST)


# Deterministic native bit circuits -------------------------------------------
# Wires 0 and 1 are constant gates. Gate creation and simplification order is
# identical to riscv_proof::circuit; no schema is accepted from the prover.


class Circuit:
    def __init__(self) -> None:
        self.gates: list[tuple] = [("constant", 0), ("constant", 1)]
        self.equalities: list[tuple[int, int]] = []

    def gate(self, *gate) -> int:
        index = len(self.gates)
        self.gates.append(gate)
        return index

    def input(self) -> int:
        return self.gate("input")

    def input_word(self, width: int) -> list[int]:
        return [self.input() for _ in range(width)]

    @staticmethod
    def constant(value: int, width: int) -> list[int]:
        return [value >> i & 1 if i < 64 else 0 for i in range(width)]

    def xor(self, a: int, b: int) -> int:
        if a == b:
            return 0
        if a == 0:
            return b
        if b == 0:
            return a
        return self.gate("xor", a, b)

    def and_(self, a: int, b: int) -> int:
        if a == 0 or b == 0:
            return 0
        if a == b or b == 1:
            return a
        if a == 1:
            return b
        return self.gate("and", a, b)

    def not_(self, a: int) -> int:
        return self.xor(a, 1)

    def or_(self, a: int, b: int) -> int:
        x = self.xor(a, b)
        y = self.and_(a, b)
        return self.xor(x, y)

    def mux(self, select: int, yes: int, no: int) -> int:
        difference = self.xor(yes, no)
        masked = self.and_(select, difference)
        return self.xor(no, masked)

    def select(self, select: int, yes: Sequence[int], no: Sequence[int]) -> list[int]:
        return [self.mux(select, a, b) for a, b in zip(yes, no, strict=True)]

    def assert_equal(self, a: int, b: int) -> None:
        self.equalities.append((a, b))

    def equals(self, a: Sequence[int], b: Sequence[int]) -> int:
        difference = 0
        for x, y in zip(a, b, strict=True):
            d = self.xor(x, y)
            difference = self.or_(difference, d)
        return self.not_(difference)

    def add_carry(self, a: Sequence[int], b: Sequence[int], carry: int) -> tuple[list[int], int]:
        out = []
        for x, y in zip(a, b, strict=True):
            propagate = self.xor(x, y)
            out.append(self.xor(propagate, carry))
            generate = self.and_(x, y)
            propagated = self.and_(propagate, carry)
            carry = self.xor(generate, propagated)
        return out, carry

    def add(self, a: Sequence[int], b: Sequence[int]) -> list[int]:
        return self.add_carry(a, b, 0)[0]

    def subtract(self, a: Sequence[int], b: Sequence[int]) -> tuple[list[int], int]:
        complement = [self.not_(bit) for bit in b]
        out, no_borrow = self.add_carry(a, complement, 1)
        return out, self.not_(no_borrow)

    def negate(self, a: Sequence[int]) -> list[int]:
        return self.subtract([0] * len(a), a)[0]

    def less_than(self, a: Sequence[int], b: Sequence[int], signed: bool = False) -> int:
        unsigned = self.subtract(a, b)[1]
        if not signed:
            return unsigned
        sign_difference = self.xor(a[-1], b[-1])
        return self.xor(unsigned, sign_difference)

    def shift(self, a: Sequence[int], amount: Sequence[int], right: bool, arithmetic: bool) -> list[int]:
        value = list(a)
        fill = a[-1] if right and arithmetic else 0
        for stage, select in enumerate(amount):
            distance = 1 << stage
            shifted = []
            for i in range(len(a)):
                source = i + distance if right else i - distance
                shifted.append(value[source] if 0 <= source < len(value) else fill)
            value = self.select(select, shifted, value)
        return value

    @staticmethod
    def extend(value: Sequence[int], width: int, signed: bool) -> list[int]:
        return list(value) + [value[-1] if signed else 0] * (width - len(value))

    def multiply(self, a: Sequence[int], b: Sequence[int], signed_a: bool, signed_b: bool) -> list[int]:
        width = len(a)
        product = [0] * (width * 2)
        for j, multiplier in enumerate(b):
            partial = [self.and_(bit, multiplier) for bit in a]
            row = [0] * (width * 2)
            row[j : j + width] = partial
            product = self.add(product, row)
        if signed_a:
            correction = [self.and_(bit, a[-1]) for bit in b]
            product[width:] = self.subtract(product[width:], correction)[0]
        if signed_b:
            correction = [self.and_(bit, b[-1]) for bit in a]
            product[width:] = self.subtract(product[width:], correction)[0]
        return product

    def divide(self, a: Sequence[int], b: Sequence[int], signed: bool) -> tuple[list[int], list[int]]:
        width = len(a)
        if signed:
            negative_a = self.negate(a)
            negative_b = self.negate(b)
            dividend = self.select(a[-1], negative_a, a)
            divisor = self.select(b[-1], negative_b, b)
        else:
            dividend, divisor = list(a), list(b)
        wide_divisor = self.extend(divisor, width + 1, False)
        remainder, quotient = [0] * (width + 1), [0] * width
        for i in reversed(range(width)):
            remainder = [dividend[i]] + remainder[:-1]
            difference, borrow = self.subtract(remainder, wide_divisor)
            quotient[i] = self.not_(borrow)
            remainder = self.select(quotient[i], difference, remainder)
        remainder = remainder[:width]
        if signed:
            sign = self.xor(a[-1], b[-1])
            negative_q = self.negate(quotient)
            quotient = self.select(sign, negative_q, quotient)
            negative_r = self.negate(remainder)
            remainder = self.select(a[-1], negative_r, remainder)
            divisor_zero = self.equals(b, [0] * width)
            quotient = self.select(divisor_zero, [1] * width, quotient)
        return quotient, remainder

    def pack(self, bits: Sequence[int]) -> int:
        return self.gate("pack", tuple(bits))

    @property
    def n_constraints(self) -> int:
        return len(self.gates) + len(self.equalities)

    def constraints(self, row: Sequence[E]) -> Iterable[E]:
        for index, gate in enumerate(self.gates):
            kind, *args = gate
            out = row[index]
            if kind == "input":
                yield out + out * out
            elif kind == "constant":
                yield out + E(args[0])
            elif kind == "xor":
                yield out + row[args[0]] + row[args[1]]
            elif kind == "and":
                yield out + row[args[0]] * row[args[1]]
            else:
                yield out + E.sum(row[bit] * E(1 << i) for i, bit in enumerate(args[0]))
        for a, b in self.equalities:
            yield row[a] + row[b]


# Encodings in the protocol's stable Opcode::ALL order.
OPCODES = (
    "Lui",
    "Auipc",
    "Jal",
    "Jalr",
    "Beq",
    "Bne",
    "Blt",
    "Bge",
    "Bltu",
    "Bgeu",
    "Lb",
    "Lh",
    "Lw",
    "Ld",
    "Lbu",
    "Lhu",
    "Lwu",
    "Sb",
    "Sh",
    "Sw",
    "Sd",
    "Addi",
    "Slti",
    "Sltiu",
    "Xori",
    "Ori",
    "Andi",
    "Slli",
    "Srli",
    "Srai",
    "Add",
    "Sub",
    "Sll",
    "Slt",
    "Sltu",
    "Xor",
    "Srl",
    "Sra",
    "Or",
    "And",
    "Addiw",
    "Slliw",
    "Srliw",
    "Sraiw",
    "Addw",
    "Subw",
    "Sllw",
    "Srlw",
    "Sraw",
    "Mul",
    "Mulh",
    "Mulhsu",
    "Mulhu",
    "Div",
    "Divu",
    "Rem",
    "Remu",
    "Mulw",
    "Divw",
    "Divuw",
    "Remw",
    "Remuw",
    "Fence",
    "Ecall",
)
ENCODINGS = (
    0x37,
    0x17,
    0x6F,
    0x67,
    0x63,
    0x1063,
    0x4063,
    0x5063,
    0x6063,
    0x7063,
    0x03,
    0x1003,
    0x2003,
    0x3003,
    0x4003,
    0x5003,
    0x6003,
    0x23,
    0x1023,
    0x2023,
    0x3023,
    0x13,
    0x2013,
    0x3013,
    0x4013,
    0x6013,
    0x7013,
    0x1013,
    0x5013,
    0x40005013,
    0x33,
    0x40000033,
    0x1033,
    0x2033,
    0x3033,
    0x4033,
    0x5033,
    0x40005033,
    0x6033,
    0x7033,
    0x1B,
    0x101B,
    0x501B,
    0x4000501B,
    0x3B,
    0x4000003B,
    0x103B,
    0x503B,
    0x4000503B,
    0x02000033,
    0x02001033,
    0x02002033,
    0x02003033,
    0x02004033,
    0x02005033,
    0x02006033,
    0x02007033,
    0x0200003B,
    0x0200403B,
    0x0200503B,
    0x0200603B,
    0x0200703B,
    0x0F,
    0x73,
)
MEMORY_WIDTHS = dict(zip(("Lb", "Lh", "Lw", "Ld", "Lbu", "Lhu", "Lwu", "Sb", "Sh", "Sw", "Sd"), (1, 2, 4, 8, 1, 2, 4, 1, 2, 4, 8)))
STORES = {"Sb", "Sh", "Sw", "Sd"}
BRANCHES = {"Beq", "Bne", "Blt", "Bge", "Bltu", "Bgeu"}


def constrain_zero_register(c: Circuit, index: Sequence[int], value: Sequence[int]) -> None:
    is_zero = c.equals(index, c.constant(0, len(index)))
    for bit in value:
        forbidden = c.and_(is_zero, bit)
        c.assert_equal(forbidden, 0)


@dataclass
class InstructionCircuit:
    circuit: Circuit
    raw: int
    raw_bits: list[int]
    pc_bits: list[int]
    pc: int
    next_pc: int
    rd: int
    rs1: int
    rs2: int
    rs1_value: int
    rs2_value: int
    rd_value: int | None
    memory_address_bits: list[int] | None
    memory_bytes: list[int]
    memory_write: bool

    @classmethod
    def build(cls, op: str) -> InstructionCircuit:
        c = Circuit()
        raw, pc, a, b = c.input_word(32), c.input_word(64), c.input_word(64), c.input_word(64)
        width = MEMORY_WIDTHS.get(op, 0)
        store = op in STORES
        load = c.input_word(width * 8) if width and not store else []
        mask = (
            0x7F
            if op in ("Lui", "Auipc", "Jal")
            else 0xFC00707F
            if op in ("Slli", "Srli", "Srai")
            else 0xFFFFFFFF
            if op == "Ecall"
            else 0xFE00707F
            if 30 <= OPCODES.index(op) <= 61 and op != "Addiw"
            else 0x707F
        )
        encoding = ENCODINGS[OPCODES.index(op)]
        for i in range(32):
            if mask >> i & 1:
                c.assert_equal(raw[i], encoding >> i & 1)
        if op == "Fence":
            normal = c.equals(raw[28:32], c.constant(0, 4))
            tso = c.equals(raw[20:32], c.constant(0x833, 12))
            legal = c.or_(normal, tso)
            c.assert_equal(legal, 1)
        c.assert_equal(pc[0], 0)
        c.assert_equal(pc[1], 0)
        for bit in pc[32:]:
            c.assert_equal(bit, 0)
        constrain_zero_register(c, raw[15:20], a)
        constrain_zero_register(c, raw[20:25], b)
        if op in ("Lui", "Auipc"):
            immediate = c.extend([0] * 12 + raw[12:32], 64, True)
        elif op == "Jal":
            immediate = c.extend([0] + raw[21:31] + [raw[20]] + raw[12:20] + [raw[31]], 64, True)
        elif op in BRANCHES:
            immediate = c.extend([0] + raw[8:12] + raw[25:31] + [raw[7], raw[31]], 64, True)
        elif store:
            immediate = c.extend(raw[7:12] + raw[25:32], 64, True)
        else:
            immediate = c.extend(raw[20:32], 64, True)
        sequential = c.add(pc, c.constant(4, 64))
        next_pc = list(sequential)
        address = None
        byte_bits = []
        result = None
        if op == "Lui":
            result = list(immediate)
        elif op == "Auipc":
            result = c.add(pc, immediate)
        elif op in ("Jal", "Jalr"):
            next_pc = c.add(pc if op == "Jal" else a, immediate)
            if op == "Jalr":
                next_pc[0] = 0
            result = sequential
        elif op in BRANCHES:
            if op in ("Beq", "Bne"):
                taken = c.equals(a, b)
                if op == "Bne":
                    taken = c.not_(taken)
            else:
                taken = c.less_than(a, b, op in ("Blt", "Bge"))
                if op in ("Bge", "Bgeu"):
                    taken = c.not_(taken)
            target = c.add(pc, immediate)
            next_pc = c.select(taken, target, next_pc)
        elif width:
            address = c.add(a, immediate)
            last_address = c.add(address, c.constant(width - 1, 64))
            for bit in address[32:]:
                c.assert_equal(bit, 0)
            for bit in last_address[32:]:
                c.assert_equal(bit, 0)
            memory = b[: width * 8] if store else load
            byte_bits = [memory[i : i + 8] for i in range(0, len(memory), 8)]
            if not store:
                result = c.extend(load, 64, op in ("Lb", "Lh", "Lw", "Ld"))
        elif op in ("Addi", "Add"):
            result = c.add(a, immediate if op == "Addi" else b)
        elif op == "Sub":
            result = c.subtract(a, b)[0]
        elif op in ("Slti", "Sltiu", "Slt", "Sltu"):
            bit = c.less_than(a, immediate if op in ("Slti", "Sltiu") else b, op in ("Slti", "Slt"))
            result = c.extend([bit], 64, False)
        elif op in ("Xori", "Ori", "Andi", "Xor", "Or", "And"):
            rhs = immediate if op in ("Xori", "Ori", "Andi") else b
            operation = c.xor if op in ("Xori", "Xor") else c.or_ if op in ("Ori", "Or") else c.and_
            result = [operation(x, y) for x, y in zip(a, rhs)]
        elif op in ("Slli", "Srli", "Srai", "Sll", "Srl", "Sra", "Slliw", "Srliw", "Sraiw", "Sllw", "Srlw", "Sraw"):
            word = op in ("Slliw", "Srliw", "Sraiw", "Sllw", "Srlw", "Sraw")
            immediate_shift = op in ("Slli", "Srli", "Srai", "Slliw", "Srliw", "Sraiw")
            bits, shift_bits = (32, 5) if word else (64, 6)
            amount = raw[20 : 20 + shift_bits] if immediate_shift else b[:shift_bits]
            value = c.shift(a[:bits], amount, op not in ("Slli", "Sll", "Slliw", "Sllw"), op in ("Srai", "Sra", "Sraiw", "Sraw"))
            result = c.extend(value, 64, word)
        elif op in ("Addiw", "Addw", "Subw"):
            value = c.subtract(a[:32], b[:32])[0] if op == "Subw" else c.add(a[:32], immediate[:32] if op == "Addiw" else b[:32])
            result = c.extend(value, 64, True)
        elif op in ("Mul", "Mulh", "Mulhsu", "Mulhu", "Mulw"):
            bits = 32 if op == "Mulw" else 64
            product = c.multiply(a[:bits], b[:bits], op in ("Mulh", "Mulhsu"), op == "Mulh")
            value = product[bits:] if op in ("Mulh", "Mulhsu", "Mulhu") else product[:bits]
            result = c.extend(value, 64, op == "Mulw")
        elif op in ("Div", "Divu", "Rem", "Remu", "Divw", "Divuw", "Remw", "Remuw"):
            word = op in ("Divw", "Divuw", "Remw", "Remuw")
            bits = 32 if word else 64
            quotient, remainder = c.divide(a[:bits], b[:bits], op in ("Div", "Rem", "Divw", "Remw"))
            value = remainder if op in ("Rem", "Remu", "Remw", "Remuw") else quotient
            result = c.extend(value, 64, word)
        else:
            require(op in ("Fence", "Ecall"), "unknown opcode")
        c.assert_equal(next_pc[0], 0)
        c.assert_equal(next_pc[1], 0)
        if result is not None:
            rd_zero = c.equals(raw[7:12], c.constant(0, 5))
            result = c.select(rd_zero, c.constant(0, 64), result)
        raw_col = c.pack(raw)
        pc_col, next_col = c.pack(pc), c.pack(next_pc)
        rd, rs1, rs2 = c.pack(raw[7:12]), c.pack(raw[15:20]), c.pack(raw[20:25])
        av, bv = c.pack(a), c.pack(b)
        rd_value = c.pack(result) if result is not None else None
        if address is not None:
            c.pack(address)
        memory_bytes = [c.pack(byte) for byte in byte_bits]
        return cls(c, raw_col, raw, pc, pc_col, next_col, rd, rs1, rs2, av, bv, rd_value, address, memory_bytes, store)


# Table coordinates use the existing degree-two Form representation.


def constant(value: int) -> Form:
    return Form({(): E(value)})


def column(index: int, scale: int = 1) -> Form:
    return Form({(index,): E(scale)})


def product(a: int, b: int, scale: int = 1) -> Form:
    return Form({tuple(sorted((a, b))): E(scale)})


def gated(enabled: int, value: Form) -> Form:
    result = Form()
    for monomial, coefficient in value.terms.items():
        require(len(monomial) <= 1, "only affine coordinates may be gated")
        key = tuple(sorted((enabled, *monomial)))
        result.terms[key] = result.terms.get(key, ZERO) + coefficient
    return result


def enabled_assert(c: Circuit, enabled: int, predicate: int) -> None:
    bad = c.not_(predicate)
    bad = c.and_(enabled, bad)
    c.assert_equal(bad, 0)


def enabled_zero(c: Circuit, enabled: int, bits: Sequence[int]) -> None:
    for bit in bits:
        bad = c.and_(enabled, bit)
        c.assert_equal(bad, 0)


@dataclass
class Flush:
    push: list[Form]
    pull: list[Form]
    count: Form | None = None


@dataclass
class Table:
    circuit: Circuit
    relations: list[Form] = field(default_factory=list)
    flushes: list[Flush] = field(default_factory=list)
    flock_slots: list[tuple[int, int]] = field(default_factory=list)

    @property
    def width(self) -> int:
        return len(self.circuit.gates)

    @property
    def n_constraints(self) -> int:
        return self.circuit.n_constraints + len(self.relations)

    def constraints(self, row: Sequence[E]) -> Iterable[E]:
        yield from self.circuit.constraints(row)
        for relation in self.relations:
            yield relation.evaluate(row.__getitem__)


class CpuTemplate:
    def __init__(self, circuit: Circuit) -> None:
        self.spec = Table(circuit)
        self.c = circuit
        self.enabled = 0

    def packed_input(self, width: int) -> tuple[list[int], int]:
        bits = self.c.input_word(width)
        return bits, self.c.pack(bits)

    def constant(self, value: int, width: int) -> int:
        return self.c.pack(self.c.constant(value, width))

    def timestamp(self, cycle: Sequence[int], slot: Sequence[int]) -> int:
        return self.c.pack([*slot, *cycle])

    def state(self, push: list[Form], pull: list[Form]) -> None:
        self.spec.flushes.append(Flush([gated(self.enabled, v) for v in push], [gated(self.enabled, v) for v in pull]))

    def event(self, ram: bool, address: Form, time: int, before: int, after: int, write: bool) -> None:
        push = [
            gated(self.enabled, constant(2 if ram else 4)),
            address,
            gated(self.enabled, column(time)),
            gated(self.enabled, column(before)),
            gated(self.enabled, column(after)),
            gated(self.enabled, constant(int(write))),
        ]
        self.spec.flushes.append(Flush(push, [constant(0) for _ in range(6)]))

    def register(self, cycle: Sequence[int], slot: int, address: int, before: int, after: int, write: bool) -> None:
        time = self.timestamp(cycle, self.c.constant(slot, 4))
        self.event(False, gated(self.enabled, column(address)), time, before, after, write)

    def ram(self, cycle: Sequence[int], slot: Sequence[int], address: Sequence[int], before: int, after: int, write: bool) -> None:
        enabled_zero(self.c, self.enabled, address[32:])
        address_column = self.c.pack(address)
        self.ram_at(cycle, slot, gated(self.enabled, column(address_column)), before, after, write)

    def ram_at(self, cycle: Sequence[int], slot: Sequence[int], address: Form, before: int, after: int, write: bool) -> None:
        time = self.timestamp(cycle, slot)
        self.event(True, address, time, before, after, write)

    def address_region(self, address: Sequence[int], width: int) -> list[Form]:
        c, e = self.c, self.enabled
        enabled_zero(c, e, address[32:])
        if width == 1:
            return [gated(e, column(c.pack(address)))]
        k = (width - 1).bit_length()
        low, high = address[:k], address[k:32]
        next_high, overflow = c.add_carry(high, c.constant(1, len(high)), 0)
        delta = [c.xor(a, b) for a, b in zip(high, next_high, strict=True)]
        high_col = c.pack(high)
        delta_col = c.pack(delta)
        addresses = []
        for offset in range(width):
            low_sum, carry = c.add_carry(low, c.constant(offset, k), 0)
            if offset == width - 1:
                end_overflow = c.and_(carry, overflow)
                enabled_zero(c, e, [end_overflow])
            low_col = c.pack(low_sum)
            masked_carry = c.and_(e, carry)
            addresses.append(product(e, low_col) + product(e, high_col, 1 << k) + product(masked_carry, delta_col, 1 << k))
        return addresses

    def cycle(self, total: int) -> tuple[list[int], int, int]:
        self.enabled = self.c.input_word(1)[0]
        bits, packed = self.packed_input(32)
        total_bits, total_column = self.packed_input(32)
        self.spec.relations.append(product(self.enabled, total_column) + column(self.enabled, total))
        wide = self.c.extend(bits, 64, False)
        bound = self.c.extend(total_bits, 64, False)
        valid = self.c.less_than(wide, bound, False)
        enabled_assert(self.c, self.enabled, valid)
        next_bits = self.c.add(wide, self.c.constant(1, 64))
        return bits, packed, self.c.pack(next_bits)

    def fetch(self, ins: InstructionCircuit) -> None:
        _, count = self.packed_input(64)
        prefix = [column(self.enabled, 8), product(self.enabled, ins.pc, 2) + column(self.enabled)]
        value = product(self.enabled, ins.raw)
        self.spec.flushes.append(
            Flush(prefix + [column(count) + product(self.enabled, count, 3), value], prefix + [column(count), value], column(count))
        )

    def syscall(self, kind: str, public: bytes, cycle: Sequence[int], cycle_col: int) -> None:
        number, argc = {"Exit": (0, 1), "ReadWitness": (1, 2), "ReadPublic": (2, 1), "Blake2s": (0x100, 4), "F192Mul": (0x101, 6)}[kind]
        a7 = self.constant(17, 5)
        number_col = self.constant(number, 64)
        self.register(cycle, 0, a7, number_col, number_col, False)
        args, argcols = [], []
        for i in range(argc):
            bits, value = self.packed_input(64)
            address = self.constant(10 + i, 5)
            self.register(cycle, 1 + i, address, value, value, False)
            args.append(bits)
            argcols.append(value)
        if kind == "F192Mul":
            terms = (((0, 0), (1, 2), (2, 1)), ((0, 1), (1, 0), (1, 2), (2, 1), (2, 2)), ((0, 2), (1, 1), (2, 0), (2, 2)))
            for i in range(3):
                output = self.packed_input(64)[1]
                address = self.constant(10 + i, 5)
                self.register(cycle, 7 + i, address, argcols[i], output, True)
                self.spec.relations.append(column(output) + Form.sum(product(argcols[j], argcols[3 + k]) for j, k in terms[i]))
            return
        if kind == "Exit":
            enabled_zero(self.c, self.enabled, args[0])
            result = self.constant(0, 64)
        elif kind == "ReadWitness":
            end, carry = self.c.add_carry(args[0], args[1], 0)
            enabled_zero(self.c, self.enabled, [carry])
            valid = self.c.less_than(end, self.c.constant(RAM_END + 1, 64), False)
            enabled_assert(self.c, self.enabled, valid)

            def state_at(index: Form) -> list[Form]:
                return [constant(64), column(cycle_col), index, column(argcols[1]), column(argcols[0])]

            self.state(state_at(constant(0)), state_at(column(argcols[1])))
            result = argcols[1]
        elif kind == "ReadPublic":
            addresses = self.address_region(args[0], len(public))
            for i, (byte, address) in enumerate(zip(public, addresses, strict=True)):
                before = self.packed_input(8)[1]
                after = self.packed_input(8)[1]
                self.spec.relations.append(product(self.enabled, after) + column(self.enabled, byte))
                slot = self.c.constant(i, 32)
                self.ram_at(cycle, slot, address, before, after, True)
            result = self.constant(32, 64)
        else:
            ranges = ((0, 64, False), (1, 32, False), (2, 16, False), (3, 32, True))
            groups = []
            slot_index = 0
            for arg, size, write in ranges:
                bits = []
                addresses = self.address_region(args[arg], size)
                for address in addresses:
                    byte_bits, value = self.packed_input(8)
                    bits.extend(byte_bits)
                    before = self.packed_input(8)[1] if write else value
                    slot = self.c.constant(slot_index, 32)
                    self.ram_at(cycle, slot, address, before, value, write)
                    slot_index += 1
                groups.append([self.c.pack(bits[i : i + 64]) for i in range(0, len(bits), 64)])
            for words, start in zip(groups, (10, 0, 18, 4), strict=True):
                self.spec.flock_slots.extend((col, start + i) for i, col in enumerate(words))
            result = self.constant(0, 64)
        a0 = self.constant(10, 5)
        self.register(cycle, 5, a0, argcols[0], result, True)


CPU_KINDS = OPCODES[:-1] + ("Exit", "ReadWitness", "ReadPublic", "Blake2s", "F192Mul", "WitnessByte")
BLAKE_TABLE, RAM_TABLE, REG_TABLE = 66, 69, 70
TABLE_COUNT = 71


def cpu_table(public: bytes, total: int, kind: str) -> Table:
    if kind == "WitnessByte":
        t = CpuTemplate(Circuit())
        cycle, cycle_col, _ = t.cycle(total)
        index, index_col = t.packed_input(32)
        length, length_col = t.packed_input(64)
        destination, destination_col = t.packed_input(64)
        wide_index = t.c.extend(index, 64, False)
        valid = t.c.less_than(wide_index, length, False)
        enabled_assert(t.c, t.enabled, valid)
        next_bits = t.c.add(wide_index, t.c.constant(1, 64))
        next_col = t.c.pack(next_bits)

        def state_at(i: int) -> list[Form]:
            return [constant(64), column(cycle_col), column(i), column(length_col), column(destination_col)]

        t.state(state_at(next_col), state_at(index_col))
        address, carry = t.c.add_carry(destination, wide_index, 0)
        enabled_zero(t.c, t.enabled, [carry])
        before = t.packed_input(8)[1]
        after = t.packed_input(8)[1]
        t.ram(cycle, index, address, before, after, True)
        return t.spec
    normal = kind in OPCODES
    ins = InstructionCircuit.build(kind if normal else "Ecall")
    t = CpuTemplate(ins.circuit)
    cycle, cycle_col, next_cycle = t.cycle(total)
    t.fetch(ins)
    exit_ = kind == "Exit"
    t.state(
        [constant(1), constant(0) if exit_ else column(ins.next_pc), column(next_cycle), constant(int(exit_))],
        [constant(1), column(ins.pc), column(cycle_col), constant(0)],
    )
    if normal:
        t.register(cycle, 0, ins.rs1, ins.rs1_value, ins.rs1_value, False)
        t.register(cycle, 1, ins.rs2, ins.rs2_value, ins.rs2_value, False)
        if ins.rd_value is not None:
            _, old = t.packed_input(64)
            t.register(cycle, 2, ins.rd, old, ins.rd_value, True)
        if ins.memory_address_bits is not None:
            addresses = t.address_region(ins.memory_address_bits, len(ins.memory_bytes))
            for i, (byte, address) in enumerate(zip(ins.memory_bytes, addresses, strict=True)):
                before = t.packed_input(8)[1] if ins.memory_write else byte
                slot = t.c.constant(i, 32)
                t.ram_at(cycle, slot, address, before, byte, ins.memory_write)
    else:
        t.syscall(kind, public, cycle, cycle_col)
    return t.spec


def equal_when(c: Circuit, enabled: int, a: Sequence[int], b: Sequence[int]) -> None:
    for x, y in zip(a, b, strict=True):
        difference = c.xor(x, y)
        violation = c.and_(enabled, difference)
        c.assert_equal(violation, 0)


def in_range(c: Circuit, address: Sequence[int], start_bits: Sequence[int], end_bits: Sequence[int]) -> int:
    below = c.less_than(address, start_bits, False)
    above = c.not_(below)
    below_end = c.less_than(address, end_bits, False)
    return c.and_(above, below_end)


def memory_table(program: ProgramInfo, ram: bool, realcount: int, logrows: int) -> Table:
    address_width, time_width, value_width = (32, 64, 8) if ram else (5, 36, 64)
    index_width = 33 if ram else 37
    c = Circuit()
    index = c.input_word(index_width)
    previous_address = c.input_word(address_width)
    previous_time = c.input_word(time_width)
    previous_value = c.input_word(value_width)
    address = c.input_word(address_width)
    time = c.input_word(time_width)
    before = c.input_word(value_width)
    after = c.input_word(value_width)
    write = c.input()
    rom_count = c.input_word(64) if ram else None
    metadata = [(realcount, index_width), (1 << logrows, index_width)]
    if ram:
        for segment in program.segments:
            metadata.extend((value, 33) for value in (segment.address, segment.address + segment.memory_size, segment.address + len(segment.data)))
    metadata_bits = [c.input_word(width) for _, width in metadata]
    in_rows = c.less_than(index, metadata_bits[1], False)
    enabled_assert(c, 1, in_rows)
    successor, overflow = c.add_carry(index, c.constant(1, len(index)), 0)
    c.assert_equal(overflow, 0)
    active = c.less_than(index, metadata_bits[0], False)
    first_row = c.equals(index, c.constant(0, len(index)))
    has_previous = c.not_(first_row)
    same_address = c.equals(previous_address, address)
    higher_address = c.less_than(previous_address, address, False)
    higher_time = c.less_than(previous_time, time, False)
    same_and_later = c.and_(same_address, higher_time)
    sorted_ = c.or_(higher_address, same_and_later)
    compare_previous = c.and_(active, has_previous)
    enabled_assert(c, compare_previous, sorted_)
    continuing = c.and_(compare_previous, same_address)
    equal_when(c, continuing, before, previous_value)
    changed_address = c.not_(same_address)
    starts_address = c.or_(first_row, changed_address)
    initialize = c.and_(active, starts_address)
    read = c.not_(write)
    reading = c.and_(active, read)
    equal_when(c, reading, before, after)
    zero_value = c.constant(0, value_width)
    lookup = 0
    if not ram:
        stack_pointer = c.equals(address, c.constant(2, address_width))
        stack_initial = c.constant(RAM_END, value_width)
        initial = c.select(stack_pointer, stack_initial, zero_value)
        equal_when(c, initialize, before, initial)
        is_zero = c.equals(address, c.constant(0, address_width))
        zero_register = c.and_(active, is_zero)
        equal_when(c, zero_register, before, zero_value)
        equal_when(c, zero_register, after, zero_value)
    else:
        wide_address = c.extend(address, 33, False)
        file_backed = 0
        for i, segment in enumerate(program.segments):
            start, memory_end, file_end = metadata_bits[2 + 3 * i : 5 + 3 * i]
            mapped = in_range(c, wide_address, start, memory_end)
            mapped_active = c.and_(active, mapped)
            if not segment.flags & 4:
                denied = c.and_(mapped_active, read)
                c.assert_equal(denied, 0)
            if not segment.flags & 2:
                denied = c.and_(mapped_active, write)
                c.assert_equal(denied, 0)
            file_ = in_range(c, wide_address, start, file_end)
            file_backed = c.or_(file_backed, file_)
        lookup = c.and_(initialize, file_backed)
        not_file = c.not_(file_backed)
        zero_initialize = c.and_(initialize, not_file)
        equal_when(c, zero_initialize, before, zero_value)
    next_address = c.select(active, address, previous_address)
    next_time = c.select(active, time, previous_time)
    next_value = c.select(active, after, previous_value)
    idx, successor_col = c.pack(index), c.pack(successor)
    pa, pt, pv = c.pack(previous_address), c.pack(previous_time), c.pack(previous_value)
    na, nt, nv = c.pack(next_address), c.pack(next_time), c.pack(next_value)
    a, tm, bv, av = c.pack(address), c.pack(time), c.pack(before), c.pack(after)
    rom = c.pack(rom_count) if rom_count is not None else None
    metadata_columns = [c.pack(bits) for bits in metadata_bits]
    separator, event_separator = (16, 2) if ram else (32, 4)
    spec = Table(c)
    spec.relations.extend(product(1, col) + column(1, value) for col, (value, _) in zip(metadata_columns, metadata, strict=True))
    spec.flushes.append(
        Flush(
            [constant(separator), column(successor_col), column(na), column(nt), column(nv)],
            [constant(separator), column(idx), column(pa), column(pt), column(pv)],
        )
    )
    spec.flushes.append(
        Flush(
            [constant(0) for _ in range(6)],
            [
                column(active, event_separator),
                product(active, a),
                product(active, tm),
                product(active, bv),
                product(active, av),
                product(active, write),
            ],
        )
    )
    if rom is not None:
        prefix, address_form, value = column(lookup, 8), product(lookup, a, 2), product(lookup, bv)
        spec.flushes.append(
            Flush([prefix, address_form, column(rom) + product(lookup, rom, 3), value], [prefix, address_form, column(rom), value], column(rom))
        )
    return spec


# Compile the fixed native circuit into Boolean R1CS wires and physical words.
# Pack nodes are linear aliases, not independent Boolean witness wires.


@dataclass
class PackedCircuit:
    k_log: int
    zero_pin: int
    gates: list[tuple]
    raw_columns: list[int]
    aliases: list[list[tuple[int, int]]]

    @classmethod
    def build(cls, circuit: Circuit, raw_columns: list[int]) -> PackedCircuit:
        gates = []
        raw_wires: list[int | None] = [None] * len(circuit.gates)

        def wire(raw: int) -> int:
            index = raw_wires[raw]
            require(index is not None, "Boolean gate references a packed word")
            return index

        for raw, gate in enumerate(circuit.gates):
            kind, *args = gate
            if kind == "pack":
                continue
            if kind == "constant":
                packed = ("one" if args[0] else "zero",)
            elif kind in ("xor", "and"):
                packed = (kind, wire(args[0]), wire(args[1]))
            else:
                packed = ("input",)
            raw_wires[raw] = len(gates)
            gates.append(packed)
        require(gates[:2] == [("zero",), ("one",)], "invalid reserved circuit wires")
        zero_pin = 0
        for a, b in circuit.equalities:
            difference = len(gates)
            gates.append(("xor", wire(a), wire(b)))
            if zero_pin == 0:
                zero_pin = difference
            else:
                sum_wire = len(gates)
                gates.append(("xor", zero_pin, difference))
                product_wire = len(gates)
                gates.append(("and", zero_pin, difference))
                zero_pin = len(gates)
                gates.append(("xor", sum_wire, product_wire))
        k_log = log2_ceil(max(1 << 10, len(gates)))
        gates.extend([("zero",)] * ((1 << k_log) - len(gates)))
        aliases = []
        for raw in raw_columns:
            gate = circuit.gates[raw]
            if gate[0] == "pack":
                aliases.append([(wire(bit), 1 << i) for i, bit in enumerate(gate[1])])
            else:
                aliases.append([(wire(raw), 1)])
        return cls(k_log, zero_pin, gates, raw_columns, aliases)


@dataclass
class PackedSpec:
    circuit: PackedCircuit
    relations: list[Form]
    flushes: list[Flush]
    flock_slots: list[tuple[int, int]]

    @classmethod
    def build(cls, spec: Table) -> PackedSpec:
        columns = {col for col, _ in spec.flock_slots}

        def collect(form: Form) -> None:
            for monomial in form.terms:
                columns.update(monomial)

        for relation in spec.relations:
            collect(relation)
        for flush in spec.flushes:
            for coord in (*flush.push, *flush.pull):
                collect(coord)
            if flush.count is not None:
                collect(flush.count)
        raw_columns = sorted(columns)
        dense = {raw: i for i, raw in enumerate(raw_columns)}

        def remap(form: Form) -> Form:
            return Form({tuple(dense[col] for col in monomial): coefficient for monomial, coefficient in form.terms.items()})

        relations = [remap(relation) for relation in spec.relations]
        flushes = [
            Flush(
                [remap(coord) for coord in flush.push],
                [remap(coord) for coord in flush.pull],
                remap(flush.count) if flush.count is not None else None,
            )
            for flush in spec.flushes
        ]
        flock_slots = [(dense[col], slot) for col, slot in spec.flock_slots]
        return cls(PackedCircuit.build(spec.circuit, raw_columns), relations, flushes, flock_slots)

    @property
    def width(self) -> int:
        return len(self.circuit.raw_columns)

    @property
    def n_constraints(self) -> int:
        return len(self.relations)

    def constraints(self, row: Sequence[E]) -> Iterable[E]:
        for relation in self.relations:
            yield relation.evaluate(row.__getitem__)


def packed_bilinear(circuit: PackedCircuit, alpha: E, rows: Sequence[E], columns: Sequence[E]) -> E:
    result = ZERO
    one_term = alpha * columns[1]
    for output, gate in enumerate(circuit.gates):
        kind, *args = gate
        if kind == "zero":
            continue
        if kind == "input":
            value = columns[output] + one_term
        elif kind == "one":
            value = columns[1] + one_term
        elif kind == "xor":
            value = columns[args[0]] + columns[args[1]] + one_term
        else:
            value = columns[args[0]] + alpha * columns[args[1]]
        result += rows[output] * value
    return result


def verify_packed(
    spec: PackedSpec, tau: int, column_point: tuple[E, ...], column_values: Sequence[E], transcript: Transcript
) -> list[tuple[tuple[E, ...], tuple[E, ...]]]:
    c = spec.circuit
    require(
        c.k_log >= 10
        and tau >= 3
        and c.k_log + tau <= MAX_STACKED_LOG + FLOCK_K_SKIP
        and len(column_point) == tau
        and len(column_values) == len(c.aliases)
        and len(c.gates) == 1 << c.k_log
        and c.zero_pin < len(c.gates),
        "invalid packed circuit shape",
    )
    zc = verify_flock_zerocheck(c.k_log + tau, transcript)
    first = verify_lincheck(zc, c.k_log, 1, c.zero_pin, lambda alpha, rows, columns: packed_bilinear(c, alpha, rows, columns), transcript)
    gamma = transcript.sample()
    psi = [ZERO] * (1 << c.k_log)
    power, target = ONE, ZERO
    for aliases, value in zip(c.aliases, column_values, strict=True):
        target += power * value
        for wire, coefficient in aliases:
            psi[wire] += power * E(coefficient)
        power *= gamma
    rounds = c.k_log - FLOCK_K_SKIP
    challenges, running = sumcheck(transcript, target, 3, [None] * rounds)
    point = tuple(reversed(challenges))
    slices = tuple(transcript.next_scalars(K_BITS))
    terminal = E.sum(weight * dot(psi[high * K_BITS : (high + 1) * K_BITS], slices) for high, weight in enumerate(eq_kernel(point)))
    require(terminal == running, "packed word projection terminal mismatch")
    return [first, (point + column_point, slices)]


# Native layout and protocol --------------------------------------------------

BUS_BITS = 4
SLOT_BITS = 8
BLAKE2S_R1CS_LOG_SIZE = 14
K_BITS = 64
FLOCK_K_SKIP = LOG_PACKING = 6
BLAKE2S_CONSTANT_COLUMN = 512


@dataclass(frozen=True)
class MemoryHeader:
    count: int
    logrows: int
    last_address: int
    last_time: int
    last_value: int

    def validate(self, ram: bool) -> None:
        expected_log = max(3, log2_ceil(self.count)) if self.count else 0
        require(self.count <= (1 << (32 if ram else 36)) and self.logrows == expected_log, "invalid memory history size")
        require(self.last_address < (RAM_END if ram else 32), "invalid terminal address")
        require(not ram or self.last_value <= 255, "invalid terminal byte")
        require(ram or self.last_time < 1 << 36, "invalid register timestamp")
        require(ram or self.last_address != 0 or self.last_value == 0, "nonzero x0 terminal value")
        require(self.count != 0 or (self.last_address, self.last_time, self.last_value) == (0, 0, 0), "nonempty terminal state for empty history")


@dataclass(frozen=True)
class Header:
    cycles: int
    log_inv_rate: int
    taus: tuple[int | None, ...]
    ram: MemoryHeader
    registers: MemoryHeader

    @classmethod
    def read(cls, transcript: Transcript) -> Header:
        def number() -> int:
            f = transcript.next_scalar()
            require(not f.c1 and not f.c2, "noncanonical header integer")
            return int(f.c0)

        cycles, rate = number(), number()
        encoded = tuple(number() for _ in range(TABLE_COUNT))
        taus = tuple(value - 1 if value else None for value in encoded)
        ram = MemoryHeader(number(), taus[RAM_TABLE] or 0, number(), number(), number())
        registers = MemoryHeader(number(), taus[REG_TABLE] or 0, number(), number(), number())
        require(0 < cycles < RAM_END and 1 <= rate <= 4 and all(tau is None or 3 <= tau <= 32 for tau in taus), "invalid native proof dimensions")
        for table, memory in ((RAM_TABLE, ram), (REG_TABLE, registers)):
            require(
                (taus[table] is None and memory.logrows == 0) if memory.count == 0 else taus[table] == memory.logrows,
                "memory table presence mismatch",
            )
        ram.validate(True)
        registers.validate(False)
        return cls(cycles, rate, taus, ram, registers)


@dataclass(frozen=True)
class PublicCoordinate:
    column: int


@dataclass
class BusBlock:
    log_rows: int
    coordinates: list[Form | PublicCoordinate]
    owner: int | None


@dataclass
class Layout:
    header: Header
    tables: list[PackedSpec]
    table_ids: list[int]
    bases: list[int]
    packed_columns: list[int]
    flock_column: int | None
    placements: list[tuple[int, int]]
    public_columns: tuple[list[int], list[int]]
    blocks: list[list[BusBlock]]
    mu: int
    flock_log: int | None

    def table_tau(self, table: int) -> int:
        tau = self.header.taus[self.table_ids[table]]
        require(tau is not None, "absent table in active layout")
        return tau

    @classmethod
    def build(cls, program: ProgramInfo, public: bytes, header: Header) -> Layout:
        tables, table_ids = [], []
        memory_boundaries = []
        for logical, tau in enumerate(header.taus):
            if tau is None:
                continue
            if logical < RAM_TABLE:
                spec = cpu_table(public, header.cycles, CPU_KINDS[logical])
            else:
                ram = logical == RAM_TABLE
                memory = header.ram if ram else header.registers
                spec = memory_table(program, ram, memory.count, memory.logrows)
                memory_boundaries.append((16 if ram else 32, memory))
            table_ids.append(logical)
            tables.append(PackedSpec.build(spec))
        entries = program.rom_entries()
        rom_addresses = [address for address, _ in entries]
        rom_values = [value for _, value in entries]
        rom_log = log2_ceil(max(1, len(rom_addresses)))
        padding = (1 << rom_log) - len(rom_addresses)
        rom_addresses.extend([(1 << 64) - 1] * padding)
        rom_values.extend([0] * padding)
        blake_tau = header.taus[BLAKE_TABLE]
        flock_log = SLOT_BITS + blake_tau if blake_tau is not None else None
        heights = [rom_log]
        flock_column = None
        if flock_log is not None:
            flock_column = len(heights)
            heights.append(flock_log)
        bases, packed_columns = [], []
        for table, logical in zip(tables, table_ids, strict=True):
            tau = header.taus[logical]
            bases.append(len(heights))
            heights.extend([tau] * table.width)
            packed_columns.append(len(heights))
            heights.append(table.circuit.k_log + tau - FLOCK_K_SKIP)
        require(all(height <= 28 for height in heights), "packed column outside PCS window")
        positions, stack_log = stack_offsets(heights)
        placements = list(zip(positions, heights, strict=True))
        mu = max(15, stack_log)
        require(mu <= 28, "committed size outside PCS window")
        blocks: list[list[BusBlock]] = [[], [], []]

        def boundary(push: list, pull: list, logrows: int) -> None:
            blocks[0].append(BusBlock(logrows, push, None))
            blocks[1].append(BusBlock(logrows, pull, None))

        boundary(
            [constant(1), constant(program.entry), constant(0), constant(0)], [constant(1), constant(0), constant(header.cycles), constant(1)], 0
        )
        boundary(
            [constant(8), PublicCoordinate(0), constant(1), PublicCoordinate(1)],
            [constant(8), PublicCoordinate(0), column(0), PublicCoordinate(1)],
            rom_log,
        )
        for separator, memory in memory_boundaries:
            boundary(
                [constant(x) for x in (separator, 0, 0, 0, 0)],
                [constant(x) for x in (separator, 1 << memory.logrows, memory.last_address, memory.last_time, memory.last_value)],
                0,
            )
        # Coordinates of owned blocks stay local, avoiding copies of every form.
        for index, table in enumerate(tables):
            tau = header.taus[table_ids[index]]
            for flush in table.flushes:
                blocks[0].append(BusBlock(tau, flush.push, index))
                blocks[1].append(BusBlock(tau, flush.pull, index))
                if flush.count is not None:
                    blocks[2].append(BusBlock(tau, [flush.count], index))
        return cls(header, tables, table_ids, bases, packed_columns, flock_column, placements, (rom_addresses, rom_values), blocks, mu, flock_log)


def selector(offset: int, low: int, point: Sequence[E]) -> E:
    result = ONE
    for bit in range(low, len(point)):
        r = point[bit]
        result *= r if offset >> bit & 1 else ONE + r
    return result


@dataclass
class Claims:
    point: tuple[E, ...]
    columns: list[tuple[int, E]]


@dataclass
class BusResult:
    claims: list[Claims]
    point: tuple[E, ...]
    forms: list[list[Form]]
    totals: list[E]


def verify_bus_balance(layout: Layout | NativeLayout, transcript: Transcript) -> BusResult:
    offsets, depths = [], []
    for blocks in layout.blocks:
        require(all(len(block.coordinates) <= 1 << BUS_BITS for block in blocks), "invalid bus tuple width")
        positions, depth = stack_offsets([block.log_rows for block in blocks])
        offsets.append(positions)
        depths.append(depth)
    require(depths[0] == depths[1] and depths[2] <= depths[0] and depths[0] < 64, "invalid bus dimensions")
    weights = eq_kernel(transcript.samples(BUS_BITS))
    beta = transcript.sample()
    count, point, values = verify_gkr_grand_products(depths[0], transcript)
    require(count != ZERO, "zero lookup count product")
    bus = BusResult([], point, [[Form() for _ in range(3)] for _ in layout.tables], list(values))
    public_cache: dict[tuple[int, int], E] = {}
    column_cache: dict[tuple[int, tuple[E, ...]], E] = {}

    def framework(coord: Form | PublicCoordinate, at: tuple[E, ...]) -> E:
        if isinstance(coord, PublicCoordinate):
            key = (coord.column, len(at))
            if key not in public_cache:
                public_cache[key] = multilinear_eval([K(x) for x in layout.public_columns[coord.column]], at)
            return public_cache[key]

        def read_column(col: int) -> E:
            key = (col, at)
            if key not in column_cache:
                value = transcript.next_scalar()
                column_cache[key] = value
                bus.claims.append(Claims(at, [(col, value)]))
            return column_cache[key]

        require(all(len(monomial) <= 1 for monomial in coord.terms), "quadratic framework coordinate")
        return coord.evaluate(read_column)

    for side, blocks in enumerate(layout.blocks):
        side_beta = ZERO if side == 2 else beta
        known, occupied = ZERO, ZERO
        for block, offset in zip(blocks, offsets[side], strict=True):
            require(block.log_rows <= len(point), "bus block exceeds cube")
            select = selector(offset, block.log_rows, point)
            occupied += select
            if block.owner is not None:
                form = bus.forms[block.owner][side]
                form.add_scaled(Form({(): side_beta}), select)
                for slot, coord in enumerate(block.coordinates):
                    weight = ONE if side == 2 and slot == 0 else ZERO if side == 2 else weights[slot]
                    form.add_scaled(coord, select * weight)
            else:
                value = side_beta
                for slot, coord in enumerate(block.coordinates):
                    weight = ONE if side == 2 and slot == 0 else ZERO if side == 2 else weights[slot]
                    value += weight * framework(coord, point[: block.log_rows])
                known += select * value
        bus.totals[side] += known + ONE + occupied
    return bus


def verify_tables(layout: Layout | NativeLayout, bus: BusResult, transcript: Transcript) -> None:
    eta = transcript.sample()
    n_constraints = sum(table.n_constraints for table in layout.tables)
    bus_power = eta**n_constraints
    form_powers = (bus_power, bus_power * eta, bus_power * eta * eta)
    claim = dot(form_powers, bus.totals)
    rounds = max((layout.table_tau(index) for index in range(len(layout.tables))), default=0)
    require(rounds <= len(bus.point), "table exceeds bus cube")
    point = [ZERO] * rounds
    table_weights = [ONE] * len(layout.tables)
    for variable in reversed(range(rounds)):
        coefficients = transcript.sumcheck_round_poly(4, claim)
        r = transcript.sample()
        point[variable] = r
        claim = poly_eval(coefficients, r)
        for i in range(len(layout.tables)):
            table_weights[i] *= ONE + bus.point[variable] + r if layout.table_tau(i) > variable else r
    terminal, constraint_power = ZERO, ONE
    for index, table in enumerate(layout.tables):
        evaluations = transcript.next_scalars(table.width)
        value = ZERO
        for identity in table.constraints(evaluations):
            value += constraint_power * identity
            constraint_power *= eta
        for form, power in zip(bus.forms[index], form_powers, strict=True):
            value += power * form.evaluate(evaluations.__getitem__)
        terminal += table_weights[index] * value
        bus.claims.append(
            Claims(tuple(point[: layout.table_tau(index)]), [(layout.bases[index] + col, value) for col, value in enumerate(evaluations)])
        )
    require(terminal == claim, "native table sumcheck terminal mismatch")


def verify_opening(layout: Layout, claims: list[Claims], root: Digest, transcript: Transcript) -> None:
    table_start = len(claims) - len(layout.tables)
    require(table_start >= 0, "missing packed table claims")
    reductions = []
    for index, table in enumerate(layout.tables):
        group = claims[table_start + index]
        bit_claims = verify_packed(table, layout.table_tau(index), group.point, [value for _, value in group.columns], transcript)
        reductions.extend((layout.packed_columns[index], point, slices) for point, slices in bit_claims)
    if layout.flock_column is not None:
        log = layout.flock_log
        require(log is not None, "missing BLAKE Flock dimensions")
        point, slices = verify_flock(log + FLOCK_K_SKIP, transcript)
        require(len(point) == log, "invalid BLAKE Flock point")
        reductions.append((layout.flock_column, point, slices))
        index = layout.table_ids.index(BLAKE_TABLE)
        group = claims[table_start + index]
        slots = []
        for local, slot in layout.tables[index].flock_slots:
            require(slot < 1 << SLOT_BITS and len(group.point) + SLOT_BITS == log, "invalid BLAKE slot dimensions")
            physical, value = group.columns[local]
            require(physical == layout.bases[index] + local, "invalid BLAKE physical column")
            point = _selector_point(slot, SLOT_BITS) + group.point
            slots.append(Claims(point, [(layout.flock_column, value)]))
        claims.extend(slots)
    else:
        require(layout.flock_log is None, "unexpected BLAKE Flock dimensions")
    ring_map = RingMap.sample(transcript)
    rings = []
    for col, point, slices in reductions:
        offset, height = layout.placements[col]
        require(height == len(point) and height <= layout.mu, "invalid packed ring dimensions")
        target, weight = ring_map.switch(point, slices)
        rings.append((offset, height, target, weight))
    for group in claims:
        for col, _ in group.columns:
            _, height = layout.placements[col]
            require(height == len(group.point) and height <= layout.mu, "invalid physical column dimensions")
    lam = transcript.sample()
    power, target = ONE, ZERO
    for _, _, value, _ in rings:
        target += power * value
        power *= lam
    for group in claims:
        for _, value in group.columns:
            target += power * value
            power *= lam

    def basis(query: Sequence[E]) -> E:
        weight, power = ZERO, ONE
        for offset, height, _, ring_weight in rings:
            weight += power * selector(offset, height, query) * ring_weight(query[:height])
            power *= lam
        for group in claims:
            height = len(group.point)
            row_weight = eq_eval(group.point, query[:height])
            for col, _ in group.columns:
                offset, _ = layout.placements[col]
                weight += power * row_weight * selector(offset, height, query)
                power *= lam
        return weight

    verify_whir(transcript, layout.mu, layout.header.log_inv_rate, target, root, basis)


# WHIR opening ----------------------------------------------------------------

INITIAL_FOLDING_FACTOR = 6
SUBSEQUENT_FOLDING_FACTOR = 4
RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 3
RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR = 1
RESIDUAL_MAX_LOG = 5
QUERY_GRINDING_BITS = 17

MIN_STACKED_LOG = 15
MAX_STACKED_LOG = 28

WHIR_QUERIES = (((223,55), (223,56,30), (223,56,31), (224,56,32), (224,56,32), (224,56,32,22), (224,56,32,22), (225,56,32,23), (225,56,32,23), (225,56,32,23,17), (226,56,32,23,17), (226,56,32,23,18), (227,56,32,23,18), (228,56,32,23,18,14)), ((112,45), (112,45,27), (112,45,28), (112,45,28), (112,45,28), (112,45,28,20), (112,45,28,20), (112,45,28,21), (112,45,28,21), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,17,13)), ((75,37), (75,37,24), (75,38,25), (75,38,25), (75,38,25), (75,38,25,18), (75,38,25,19), (75,38,25,19), (75,38,25,19), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (76,38,25,19,16,13)), ((56,32), (56,32,22), (56,32,22), (56,32,23), (56,32,23), (56,32,23,17), (56,32,23,17), (56,32,23,18), (56,32,23,18), (57,32,23,18,14), (57,32,23,18,14), (57,32,23,18,15), (57,33,23,18,15), (57,33,23,18,15,12)))  # fmt: skip


@dataclass(frozen=True)
class WhirConfig:
    log_inv_rates: tuple[int, ...]
    folds: tuple[int, ...]
    queries: tuple[int, ...]


def derive_config(log_n: int, log_inv_rate: int) -> WhirConfig:
    """The opening shape at this size and rate: the ladder geometry, then the
    tabulated query counts."""
    require(MIN_STACKED_LOG <= log_n <= MAX_STACKED_LOG and 1 <= log_inv_rate <= 4, "invalid WHIR shape")
    folds = [INITIAL_FOLDING_FACTOR]
    log_inv_rates = [log_inv_rate]
    remaining = log_n - INITIAL_FOLDING_FACTOR
    while remaining > RESIDUAL_MAX_LOG:
        first = len(folds) == 1
        log_inv_rates.append(log_inv_rates[-1] + folds[-1] - (RS_DOMAIN_INITIAL_REDUCTION_FACTOR if first else RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR))
        fold = min(SUBSEQUENT_FOLDING_FACTOR, remaining)
        remaining -= fold
        folds.append(fold)
    queries = WHIR_QUERIES[log_inv_rate - 1][log_n - MIN_STACKED_LOG]
    require(len(queries) == len(folds), "tabulated query count does not match the ladder")
    return WhirConfig(log_inv_rates=tuple(log_inv_rates), folds=tuple(folds), queries=queries)


def _ext_row(words: Sequence[K]) -> tuple[E, ...]:
    """Regroup a level's leaf words into the E values they encode, three per lane."""
    return tuple(E(*words[i : i + 3]) for i in range(0, len(words), 3))


def sample_queries(transcript: Transcript, block_length: int, count: int) -> list[int]:
    depth = log2_strict(block_length)
    per_word = 192 // depth
    result: list[int] = []
    while len(result) < count:
        bits = int(transcript.sample())
        for chunk in range(min(per_word, count - len(result))):
            result.append((bits >> (chunk * depth)) & (block_length - 1))
    return result


def _enforced_sum(rows: Sequence[Sequence[K | E]], folds: Sequence[E], query_weights: Sequence[E]) -> E:
    lane_weights = eq_kernel(folds)
    total = ZERO
    for query_weight, row in zip(query_weights, rows, strict=True):
        total += query_weight * dot(row, lane_weights)
    return total


def _subspace_roots(log_n: int) -> list[E]:
    roots = [ONE]
    layer = [E(2**i) for i in range(1, log_n + 1)]
    for _ in range(log_n):
        layer = [value**2 + roots[-1] * value for value in layer]
        roots.append(layer.pop(0))
    return roots


def _induced_weight(message_log: int, queries: Sequence[int], query_weights: Sequence[E], point: Sequence[E]) -> E:
    """The level's batched query claims, as one weight at `point`.

    Each query contributes the novel-basis column weight of doc annex B, Lemma
    lem:colweight, `prod_k (1 + p_k (1 + W-hat_k(x_q)))`, scaled by its power of
    the level's batching challenge.
    """
    require(len(point) == message_log, "bad induced-basis dimensions")
    roots = _subspace_roots(message_log)
    inverses = [value.inv() if value else ZERO for value in roots]
    total = ZERO
    for weight, query in zip(query_weights, queries, strict=True):
        basis = E(query)
        product = weight
        for coordinate, challenge in enumerate(point):
            product *= ONE + challenge * (ONE + basis * inverses[coordinate])
            basis = basis**2 + roots[coordinate] * basis
        total += product
    return total


@dataclass(frozen=True)
class GluedClaim:
    """One claim folded into the running sumcheck, and the weight it owes back.

    A level's batched queries and an out-of-domain claim differ only in that
    weight: both are a power of the level's lambda times a function of the
    terminal point, restricted to the level's own message coordinates.
    """

    scalar: E  # the power of lambda it was glued with
    fold_start: int  # how many fold challenges preceded the level
    weight_at: Callable[[Sequence[E]], E]


def verify_whir(
    transcript: Transcript, log_n: int, log_inv_rate: int, target: E, root: Digest, evaluate_basis: Callable[[Sequence[E]], E], l0_lanes: int = 64
) -> None:
    """Verify the base-field multilevel opening with a one-point terminal check."""
    config = derive_config(log_n, log_inv_rate)
    require(1 <= l0_lanes <= 64, "invalid committed lane count")
    levels = len(config.folds)

    running_quad = transcript.sumcheck_round_poly(3, target)
    folds: list[E] = []
    glued: list[GluedClaim] = []
    current_root = root

    for level, (fold_count, level_rate) in enumerate(zip(config.folds, config.log_inv_rates, strict=True)):
        level_folds: list[E] = []
        for _ in range(fold_count):
            challenge = transcript.sample()
            folds.append(challenge)
            level_folds.append(challenge)
            running_quad = transcript.sumcheck_round_poly(3, poly_eval(running_quad, challenge))

        message_log = log_n - len(folds)
        final_level = level == levels - 1
        # The level's claims, held until its batching challenge is drawn: the
        # OOD claims first, then the query batch (Annex B, Protocol 1 step 1).
        pending: list[tuple[Sequence[E], Callable[[Sequence[E]], E]]] = []
        if final_level:
            residual = tuple(transcript.next_scalars(2**message_log))
        else:
            next_root = Digest.from_halves(*transcript.next_scalars(2))
            ood_point = tuple(transcript.samples(message_log))
            ood_value = transcript.next_scalar()
            pending.append((transcript.sumcheck_round_poly(3, ood_value), lambda x, z=ood_point: eq_eval(z, x)))

        transcript.grind_check(QUERY_GRINDING_BITS)
        block_length = 2 ** (message_log + level_rate)
        queries = sample_queries(transcript, block_length, config.queries[level])
        # One batching challenge per level, drawn once every claim it batches is
        # fixed: the OOD claims above and these query positions.
        lam = transcript.sample()
        query_weights = powers(lam, len(queries))
        # Level 0 committed the K witness, one leaf word per lane; every deeper
        # level a folded E one, three words per lane.
        lanes = 2**fold_count
        words = transcript.merkle(current_root, block_length, queries, lanes if level == 0 else 3 * lanes)
        if level == 0:
            require(all(not word for row in words for word in row[: 64 - l0_lanes]), "nonzero pruned level-zero prefix")
        rows: list[Sequence[K | E]] = [tuple(reversed(row)) for row in words] if level == 0 else [_ext_row(row) for row in words]
        enforced = _enforced_sum(rows, level_folds, query_weights)

        # Every commitment, including the last one, enters through an intro
        # message; the level's claims are then batched with powers of `lam`,
        # the running claim keeping lam^0 = 1.
        batch = (message_log, tuple(queries), tuple(query_weights))
        pending.append((transcript.sumcheck_round_poly(3, enforced), lambda x, b=batch: _induced_weight(*b, x)))
        scalar = ONE
        for intro, weight_at in pending:
            scalar *= lam
            running_quad = [q + scalar * i for q, i in zip(running_quad, intro, strict=True)]
            glued.append(GluedClaim(scalar, len(folds), weight_at))

        if final_level:
            # Finish the remaining sumcheck rounds and close on one evaluation
            # of every basis at the resulting point.
            tail_folds: list[E] = []
            for round_index in range(message_log):
                challenge = transcript.sample()
                running_target = poly_eval(running_quad, challenge)
                tail_folds.append(challenge)
                if round_index + 1 < message_log:
                    running_quad = transcript.sumcheck_round_poly(3, running_target)
            # Each glued claim is rebound at the terminal point: the fold
            # challenges its level fixed after it was made, then the tail.
            point = folds + tail_folds
            lane_folds = config.folds[0]
            weight = evaluate_basis(point[lane_folds:] + point[:lane_folds])
            for claim in glued:
                weight += claim.scalar * claim.weight_at(folds[claim.fold_start :] + tail_folds)
            terminal = weight * multilinear_eval(residual, tail_folds)
            require(terminal == running_target, "WHIR terminal check failed")
            return
        current_root = next_root

    raise VerificationError("WHIR verification ended without a terminal level")


# Flock reduction -------------------------------------------------------------

PHI_BASIS = (E(0x0000000000000001), E(0x033CE8BEDDC8A656), E(0x512620375ED2A108), E(0x0C9E636090AAFC01), E(0xBA4F3CD82801769C), E(0xBA26E7904ADB4A47), E(0x467698598926DC01), E(0x4418AE808B28BDD0))  # fmt: skip
PHI = tuple(E.sum(PHI_BASIS[bit] for bit in range(8) if value >> bit & 1) for value in range(256))

_MEDIUM_GENERATOR = E(0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0)

FIXED_CHALLENGES = (
    PHI[0xF7], PHI[0x53], PHI[0xB5],
    *tuple(_MEDIUM_GENERATOR ** (2**power) / (ONE + _MEDIUM_GENERATOR ** (2**power)) for power in range(4)),
)  # fmt: skip


@cache
def _window_denominator(count: int) -> E:
    """The one barycentric denominator `PHI[:count]` has: `prod_(k != 0) PHI[k]`, inverted.

    PHI is F2-linear in its index, so `PHI[i] + PHI[j] = PHI[i ^ j]`, and over a power-of-two prefix
    `j -> i ^ j` only permutes the block. Every node is left the same product.
    """
    return reduce(mul, PHI[1:count], ONE).inv()


def lagrange_weights(count: int, point: E) -> list[E]:
    """The barycentric weights of `PHI[:count]` at `point`, by prefix and suffix numerator products."""
    differences = [point + node for node in PHI[:count]]
    prefix = list(accumulate(differences, mul, initial=ONE))
    suffix = list(accumulate(reversed(differences), mul, initial=ONE))[::-1]
    denominator = _window_denominator(count)
    return [p * s * denominator for p, s in zip(prefix[:count], suffix[1:])]


def lagrange_interpolate(count: int, values: Sequence[E], point: E) -> E:
    return dot(lagrange_weights(count, point), values)


@dataclass(frozen=True)
class ZerocheckResult:
    z_skip: E
    chi: MultilinearPoint
    v_a: E
    v_b: E
    v_c: E


def verify_flock_zerocheck(log_n: int, transcript: Transcript) -> ZerocheckResult:
    """The zerocheck: one univariate skip round, then nflock quadratic ones.
    C rides those rounds with AB, so all three claims come out at one point."""
    require(FLOCK_K_SKIP + 7 <= log_n <= MAX_STACKED_LOG + FLOCK_K_SKIP, "invalid Flock dimensions")
    # The point r: seven fixed coordinates, the rest sampled.
    r = (*FIXED_CHALLENGES, *transcript.samples(log_n - FLOCK_K_SKIP - len(FIXED_CHALLENGES)))

    # P = P^AB + P^C on the coset, then z_skip; the 64 zeros on Lambda are assumed.
    p_coset = transcript.next_scalars(K_BITS)
    z_skip = transcript.sample()
    v_p = lagrange_interpolate(2 * K_BITS, [ZERO] * K_BITS + list(p_coset), z_skip)

    # nflock quadratic rounds on P, closed by v_a, v_b.
    chi, running = sumcheck(transcript, v_p, 3, r)
    v_a, v_b = transcript.next_scalars(2)
    v_c = running + v_a * v_b
    return ZerocheckResult(z_skip, chi, v_a, v_b, v_c)


def verify_lincheck(
    zc: ZerocheckResult, k_log: int, one_pin: int, zero_pin: int | None, bilinear: Callable[[E, Sequence[E], Sequence[E]], E], transcript: Transcript
) -> tuple[MultilinearPoint, tuple[E, ...]]:
    require(FLOCK_K_SKIP <= k_log <= MAX_STACKED_LOG, "invalid lincheck circuit size")
    rounds = k_log - FLOCK_K_SKIP
    width = 1 << k_log
    require(one_pin < width and (zero_pin is None or zero_pin < width) and rounds <= len(zc.chi) <= MAX_STACKED_LOG, "invalid lincheck dimensions")
    alpha = transcript.sample()
    alpha2 = alpha * alpha
    alpha3 = alpha2 * alpha
    skip_weights = lagrange_weights(K_BITS, zc.z_skip)
    chi_in = zc.chi[:rounds]
    e_row = [weight * value for weight in eq_kernel(chi_in) for value in skip_weights]
    claim = zc.v_a + alpha * zc.v_b + alpha2 * zc.v_c + alpha3
    challenges, running = sumcheck(transcript, claim, 3, [None] * rounds)
    slices = tuple(transcript.next_scalars(K_BITS))
    point = tuple(reversed(challenges))
    w_col = [weight * value for weight in eq_kernel(point) for value in slices]
    terminal = bilinear(alpha, e_row, w_col) + alpha2 * eq_eval(chi_in, point) * dot(skip_weights, slices) + alpha3 * w_col[one_pin]
    if zero_pin is not None:
        terminal += alpha2 * alpha2 * w_col[zero_pin]
    require(terminal == running, "Flock lincheck terminal mismatch")
    return point + zc.chi[rounds:], slices


def verify_flock_lincheck(zc: ZerocheckResult, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, ...]]:
    return verify_lincheck(zc, BLAKE2S_R1CS_LOG_SIZE, BLAKE2S_CONSTANT_COLUMN, None, blake2s_bilinear, transcript)


def blake2s_row_values(column_weights: Sequence[E]) -> tuple[list[E], list[E]]:
    """Compute `A0 w` and `B0 w` by one forward walk of the circuit."""
    size = 2**BLAKE2S_R1CS_LOG_SIZE
    constant = BLAKE2S_CONSTANT_COLUMN
    message_base = 640
    counter_low = 1152
    counter_high = 1184
    final_flag = 1216
    last_node_flag = 1248
    gates_base = 1280
    gate_stride = 184
    left_values = [ZERO] * size
    right_values = [ZERO] * size

    def slots(base: int) -> tuple[E, ...]:
        return tuple(column_weights[base + bit] for bit in range(32))

    def literal(value: int) -> tuple[E, ...]:
        return tuple(column_weights[constant] if value >> bit & 1 else ZERO for bit in range(32))

    def xor(x: Sequence[E], y: Sequence[E]) -> tuple[E, ...]:
        return tuple(a + b for a, b in zip(x, y, strict=True))

    def rotate_right(word: Sequence[E], amount: int) -> tuple[E, ...]:
        return tuple(word[(bit + amount) & 31] for bit in range(32))

    def add(x: Sequence[E], y: Sequence[E], carry_base: int) -> tuple[E, ...]:
        carry = ZERO
        output = []
        for bit in range(32):
            if bit < 31:
                left_values[carry_base + bit] = x[bit] + carry
                right_values[carry_base + bit] = y[bit] + carry
            output.append(x[bit] + y[bit] + carry)
            if bit < 31:
                carry += column_weights[carry_base + bit]
        return tuple(output)

    def add3(x: Sequence[E], y: Sequence[E], z: Sequence[E], base: int) -> tuple[E, ...]:
        """Fused three-operand add: 31 majority rows then 30 ripple rows.

        The majority of bit `i` is `maj_aux[i] + z[i]`, since over GF(2)
        `(x+z)(y+z) = xy + xz + yz + z`; then `x + y + z` is the ripple sum of
        `p = x^y^z` against `q[i] = maj[i-1]`, whose bit 0 is zero, so the
        ripple layer's bit 0 needs no row and slot `base + 31 + i - 1` carries
        bit `i`.
        """
        majority = []
        for bit in range(31):
            left_values[base + bit] = x[bit] + z[bit]
            right_values[base + bit] = y[bit] + z[bit]
            majority.append(column_weights[base + bit] + z[bit])
        ripple_base = base + 31
        carry = ZERO
        output = []
        for bit in range(32):
            q = ZERO if bit == 0 else majority[bit - 1]
            left = x[bit] + y[bit] + z[bit] + carry
            output.append(left + q)
            if 1 <= bit <= 30:
                left_values[ripple_base + bit - 1] = left
                right_values[ripple_base + bit - 1] = q + carry
                carry += column_weights[ripple_base + bit - 1]
        return tuple(output)

    def linear_rows(values: Sequence[E], base: int) -> None:
        for bit in range(32):
            left_values[base + bit] = values[bit]
            right_values[base + bit] = column_weights[constant]

    for base, length in ((0, 256), (message_base, 512), (counter_low, 128)):
        for row in range(base, base + length):
            left_values[row] = column_weights[row]
            right_values[row] = column_weights[constant]

    # v[0..8] = h, v[8..12] = IV[0..4], v[12..16] = IV[4..8] ^ (t_lo, t_hi, f0, f1).
    state = [slots(32 * word) for word in range(8)]
    state.extend(literal(BLAKE2S_IV[word]) for word in range(4))
    state.extend(xor(literal(BLAKE2S_IV[4 + word]), slots(base)) for word, base in enumerate((counter_low, counter_high, final_flag, last_node_flag)))

    for round_index in range(10):
        sigma = BLAKE2S_SIGMA[round_index]
        for gate_index, (lane_a, lane_b, lane_c, lane_d) in enumerate(BLAKE2S_G_LANES):
            gate = round_index * 8 + gate_index
            gate_base = gates_base + gate_stride * gate
            a, b, c, d = state[lane_a], state[lane_b], state[lane_c], state[lane_d]
            mx = slots(message_base + 32 * sigma[2 * gate_index])
            my = slots(message_base + 32 * sigma[2 * gate_index + 1])
            a1 = add3(a, b, mx, gate_base)
            d1 = rotate_right(xor(d, a1), 16)
            c1 = add(c, d1, gate_base + 61)
            b1 = rotate_right(xor(b, c1), 12)
            a2 = add3(a1, b1, my, gate_base + 92)
            d2 = rotate_right(xor(d1, a2), 8)
            c2 = add(c1, d2, gate_base + 153)
            b2 = rotate_right(xor(b1, c2), 7)
            # Every lane cascades: this encoding materializes no intermediate word.
            state[lane_a] = a2
            state[lane_b] = b2
            state[lane_c] = c2
            state[lane_d] = d2

    # out[w] = h[w] ^ v[w] ^ v[w+8], the only materialized words.
    for word in range(8):
        out = xor(xor(state[word], state[word + 8]), slots(32 * word))
        linear_rows(out, 256 + 32 * word)

    left_values[constant] = column_weights[constant]
    right_values[constant] = column_weights[constant]
    return left_values, right_values


def blake2s_bilinear(alpha: E, row_weights: Sequence[E], column_weights: Sequence[E]) -> E:
    """Compute `e_row^T (A0 + alpha B0) w_col` from the two forward row vectors."""
    left_values, right_values = blake2s_row_values(column_weights)
    return dot(row_weights, left_values) + alpha * dot(row_weights, right_values)


def verify_flock(log_n: int, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, ...]]:
    """The reduction in protocol order: zerocheck, then lincheck. What it leaves is the
    point and the 64 claims s[i] = z(i, point), i < 64, for ring switching to bind."""
    zc = verify_flock_zerocheck(log_n, transcript)
    return verify_flock_lincheck(zc, transcript)


# Ring switching --------------------------------------------------------------

# The Frobenius shifts of the six stages composing Phi, one challenge each.
RING_MAP_SHIFTS = (32, 16, 8, 4, 2, 1)


def _phi(value: E, challenges: Sequence[E]) -> E:
    """The drawn map, stage by stage: `a_p+1 = a_p + f_p a_p^(2^shift)`."""
    for challenge, shift in zip(challenges, RING_MAP_SHIFTS, strict=True):
        value += challenge * value ** (2**shift)
    return value


def _ring_weight(r: MultilinearPoint, r_prime: Sequence[E], coefficients: Sequence[E]) -> E:
    """The weight `W(u) = Phi(eq(r, u))`, extended and evaluated by the opening at
    `r_prime`: `sum_k c_k prod_n (1 + r_n^(2^k) + r'_n)`."""
    total = ZERO
    frobenius = list(r)
    for c in coefficients:
        product = c
        for value, challenge in zip(frobenius, r_prime, strict=True):
            product *= ONE + value + challenge
        total += product
        frobenius = [value**2 for value in frobenius]
    return total


@dataclass(frozen=True)
class RingMap:
    challenges: tuple[E, ...]
    coefficients: tuple[E, ...]

    @classmethod
    def sample(cls, transcript: Transcript) -> RingMap:
        challenges = tuple(transcript.samples(len(RING_MAP_SHIFTS)))
        coefficients = [ONE] * K_BITS
        for challenge, shift in zip(challenges, RING_MAP_SHIFTS, strict=True):
            power = challenge
            for exponent in range(shift):
                for k in range(shift + exponent, K_BITS, 2 * shift):
                    coefficients[k] *= power
                power *= power
        return cls(challenges, tuple(coefficients))

    def switch(self, point: MultilinearPoint, slices: Sequence[E]) -> tuple[E, Callable[[Sequence[E]], E]]:
        require(len(slices) == K_BITS and len(point) <= MAX_STACKED_LOG, "invalid ring slice dimensions")
        target = poly_eval([_phi(value, self.challenges) for value in slices], GEN)
        return target, lambda query: _ring_weight(point, query, self.coefficients)


# Field-native circuit keys ---------------------------------------------------

NATIVE_KEY_DOMAIN = b"leanVM/native-circuit/key/v2\0"
NATIVE_PUBLIC_DOMAIN = b"leanVM/native-circuit/public/v2\0"
NATIVE_KEY_WORDS = 77
NATIVE_KINDS = (
    "Constant",
    "PublicInput",
    "PrivateInput",
    "Add",
    "Mul",
    "Inverse",
    "Limb0",
    "Limb1",
    "Limb2",
    "Compose",
    "AssertEqual",
    "AssertBool",
    "Blake2s",
)


@dataclass
class NativeTable:
    kind: str
    fixed: int
    width: int
    relations: list[Form]
    flushes: list[Flush]
    flock_slots: list[tuple[int, int]]

    @property
    def n_constraints(self) -> int:
        return len(self.relations)

    def constraints(self, row: Sequence[E]) -> Iterable[E]:
        return (relation.evaluate(row.__getitem__) for relation in self.relations)


def native_schema(kind: str) -> NativeTable:
    """The thirteen immutable schemas in recursion/tables.rs, not proof data."""
    ports = {
        "Constant": 1,
        "PublicInput": 1,
        "PrivateInput": 1,
        "Add": 3,
        "Mul": 3,
        "Inverse": 2,
        "Limb0": 2,
        "Limb1": 2,
        "Limb2": 2,
        "Compose": 4,
        "AssertEqual": 2,
        "AssertBool": 1,
        "Blake2s": 18,
    }[kind]
    extra = 1 + 3 * ports
    fixed = extra + (3 if kind == "Constant" else 1 if kind == "PublicInput" else 0)
    table = NativeTable(kind, fixed, fixed + 3 * ports, [], [], [])

    def col(port: int, limb: int) -> int:
        return fixed + 3 * port + limb

    def coordinates(port: int, counter: int) -> list[Form]:
        return [column(0, 128), column(1 + 3 * port), column(counter), *(product(0, col(port, limb)) for limb in range(3))]

    for port in range(ports):
        metadata = 1 + 3 * port
        table.flushes.append(Flush(coordinates(port, metadata + 1), coordinates(port, metadata + 2)))
    if kind == "Constant":
        table.relations = [column(col(0, limb)) + column(extra + limb) for limb in range(3)]
    elif kind == "PublicInput":
        table.flushes.append(
            Flush([constant(0) for _ in range(5)], [column(0, 256), column(extra), *(product(0, col(0, limb)) for limb in range(3))])
        )
    elif kind == "Add":
        table.relations = [Form.sum(column(col(port, limb)) for port in range(3)) for limb in range(3)]
    elif kind in ("Mul", "Inverse"):
        terms = (((0, 0), (1, 2), (2, 1)), ((0, 1), (1, 0), (1, 2), (2, 1), (2, 2)), ((0, 2), (1, 1), (2, 0), (2, 2)))
        lhs, rhs = (1, 2) if kind == "Mul" else (0, 1)
        for limb, pairs in enumerate(terms):
            relation = Form.sum(product(col(lhs, i), col(rhs, j)) for i, j in pairs)
            if kind == "Mul":
                relation += column(col(0, limb))
            elif limb == 0:
                relation += column(0)
            table.relations.append(relation)
    elif kind.startswith("Limb"):
        limb = int(kind[-1])
        table.relations = [column(col(0, 0)) + column(col(1, limb)), column(col(0, 1)), column(col(0, 2))]
    elif kind == "Compose":
        for limb in range(3):
            table.relations.extend((column(col(0, limb)) + column(col(limb + 1, 0)), column(col(limb + 1, 1)), column(col(limb + 1, 2))))
    elif kind == "AssertEqual":
        table.relations = [column(col(0, limb)) + column(col(1, limb)) for limb in range(3)]
    elif kind == "AssertBool":
        a = col(0, 0)
        table.relations = [
            product(a, a) + column(a),
            product(a + 2, a + 2) + column(a + 1),
            product(a + 1, a + 1) + product(a + 2, a + 2) + column(a + 2),
        ]
    elif kind == "Blake2s":
        for port in range(18):
            table.relations.extend((column(col(port, 1)), column(col(port, 2))))
            slot = 4 + port if port < 4 else port + 6 if port < 12 else port - 12 if port < 16 else port + 2
            table.flock_slots.append((col(port, 0), slot))
    return table


@dataclass
class NativeLayout:
    tables: list[NativeTable]
    taus: list[int]
    bases: list[int]
    blocks: list[list[BusBlock]]
    # Physical column -> (fixed stack?, offset, dimension).
    columns: list[tuple[bool, int, int]]
    fixed_mu: int
    fixed_lanes: int
    private_mu: int
    private_lanes: int
    fixed_root: Digest
    flock: tuple[int, int, int] | None

    def table_tau(self, index: int) -> int:
        return self.taus[index]

    @classmethod
    def build(cls, descriptor: Sequence[int], public: Sequence[E]) -> NativeLayout:
        require(len(descriptor) == NATIVE_KEY_WORDS, "native key descriptor must have 77 words")
        require(all(type(word) is int and 0 <= word < 2**64 for word in descriptor), "invalid native key word")
        require(descriptor[0] == len(public), "native public field count mismatch")
        tables, taus, bases, entries = [], [], [], []
        fixed_logs, private_logs = [], []
        blocks: list[list[BusBlock]] = [[], [], []]
        width = 0
        for index, kind in enumerate(NATIVE_KINDS):
            entry = tuple(descriptor[12 + 5 * index : 17 + 5 * index])
            present, tau, _, _, _ = entry
            require(present in (0, 1), "invalid native table presence")
            if not present:
                require(entry == (0, 0, 0, 0, 0), "noncanonical absent native table")
                continue
            require(3 <= tau <= MAX_STACKED_LOG, "invalid native table dimension")
            table = native_schema(kind)
            owner = len(tables)
            tables.append(table)
            taus.append(tau)
            bases.append(width)
            entries.append(entry)
            width += table.width
            fixed_logs.extend([tau] * table.fixed)
            private_logs.extend([tau] * (table.width - table.fixed))
            for flush in table.flushes:
                blocks[0].append(BusBlock(tau, flush.push, owner))
                blocks[1].append(BusBlock(tau, flush.pull, owner))
        require(bool(tables), "empty native key")
        flock_index = next((i for i, table in enumerate(tables) if table.kind == "Blake2s"), None)
        if flock_index is not None:
            private_logs.append(taus[flock_index] + SLOT_BITS)
        require(
            sum(2**n for n in fixed_logs) <= 2**MAX_STACKED_LOG and sum(2**n for n in private_logs) <= 2**MAX_STACKED_LOG,
            "native stack exceeds capacity",
        )
        fixed_offsets, fixed_mu = stack_offsets(fixed_logs)
        private_offsets, private_mu = stack_offsets(private_logs)
        fixed_mu, private_mu = max(MIN_STACKED_LOG, fixed_mu), max(MIN_STACKED_LOG, private_mu)

        def lane_count(logs: Sequence[int], mu: int) -> int:
            lane_size = 2 ** (mu - INITIAL_FOLDING_FACTOR)
            return max(1, (sum(2**n for n in logs) + lane_size - 1) // lane_size)

        fixed_lanes, private_lanes = lane_count(fixed_logs, fixed_mu), lane_count(private_logs, private_mu)
        bus_offsets, _ = stack_offsets([block.log_rows for block in blocks[0]])
        public_offset = sum(2**block.log_rows for block in blocks[0])
        bus_mu = log2_ceil(public_offset + len(public))
        flock_offset = private_offsets[-1] if flock_index is not None else 0
        require(
            tuple(descriptor[:8]) == (len(public), fixed_mu, fixed_lanes, private_mu, private_lanes, bus_mu, public_offset, flock_offset),
            "noncanonical native stack layout",
        )
        columns = []
        fixed_start = private_start = bus_start = 0
        for table, tau, entry in zip(tables, taus, entries, strict=True):
            require(
                entry[2:] == (fixed_offsets[fixed_start], private_offsets[private_start], bus_offsets[bus_start]),
                "noncanonical native table placement",
            )
            columns.extend((True, fixed_offsets[fixed_start + i], tau) for i in range(table.fixed))
            columns.extend((False, private_offsets[private_start + i], tau) for i in range(table.width - table.fixed))
            fixed_start += table.fixed
            private_start += table.width - table.fixed
            bus_start += len(table.flushes)
        counter = ONE
        for value in public:
            require(isinstance(value, E), "native public values must be F192 elements")
            coordinates = [constant(256), constant(int(counter.c0)), constant(int(value.c0)), constant(int(value.c1)), constant(int(value.c2))]
            blocks[0].append(BusBlock(0, coordinates, None))
            blocks[1].append(BusBlock(0, [constant(0) for _ in range(5)], None))
            counter *= GEN
        flock = None if flock_index is None else (flock_index, flock_offset, taus[flock_index] + SLOT_BITS)
        return cls(
            tables, taus, bases, blocks, columns, fixed_mu, fixed_lanes, private_mu, private_lanes, Digest(pack("<4Q", *descriptor[8:12])), flock
        )


def verify_native_stack(
    transcript: Transcript,
    log_n: int,
    lanes: int,
    rate: int,
    root: Digest,
    points: Sequence[tuple[int, MultilinearPoint, E]],
    reductions: Sequence[tuple[int, MultilinearPoint, tuple[E, ...]]],
) -> None:
    rings = []
    if reductions:
        ring_map = RingMap.sample(transcript)
        rings = [(offset, point, *ring_map.switch(point, slices)) for offset, point, slices in reductions]
    lam = transcript.sample()
    power, target = ONE, ZERO
    for _, _, value, _ in rings:
        target += power * value
        power *= lam
    for _, _, value in points:
        target += power * value
        power *= lam

    def basis(query: Sequence[E]) -> E:
        power, result = ONE, ZERO
        for offset, point, _, weight in rings:
            result += power * selector(offset, len(point), query) * weight(query[: len(point)])
            power *= lam
        for offset, point, _ in points:
            result += power * selector(offset, len(point), query) * eq_eval(point, query[: len(point)])
            power *= lam
        return result

    verify_whir(transcript, log_n, rate, target, root, basis, lanes)


def verify_native(expected_descriptor: Sequence[int], public: Sequence[E], proof: Proof) -> None:
    """Verify against a trusted circuit descriptor, never a proof-supplied key.

    The descriptor is Key::descriptor(), 77 little-endian u64 words. Public
    inputs are F192 values in circuit order. Proof uses expanded RV64PRF1 paths.
    """
    layout = NativeLayout.build(expected_descriptor, public)
    key_digest = blake2s_hash(blake2s_hash(NATIVE_KEY_DOMAIN).value + pack("<77Q", *expected_descriptor))
    public_digest = blake2s_hash(blake2s_hash(NATIVE_PUBLIC_DOMAIN).value + pack("<Q", len(public)) + b"".join(value.to_bytes() for value in public))
    transcript = Transcript(proof, key_digest, public_digest)
    rate = transcript.next_scalar()
    require(not rate.c1 and not rate.c2 and 1 <= int(rate.c0) <= 4, "invalid native private PCS rate")
    root = Digest.from_halves(*transcript.next_scalars(2))
    bus = verify_bus_balance(layout, transcript)
    verify_tables(layout, bus, transcript)
    fixed, private = [], []
    for group in bus.claims:
        for col, value in group.columns:
            is_fixed, offset, height = layout.columns[col]
            require(height == len(group.point), "invalid native column claim dimension")
            (fixed if is_fixed else private).append((offset, group.point, value))
    reductions = []
    if layout.flock is not None:
        index, offset, height = layout.flock
        group = bus.claims[index]
        for local, slot in layout.tables[index].flock_slots:
            private.append((offset, _selector_point(slot, SLOT_BITS) + group.point, group.columns[local][1]))
        point, slices = verify_flock(height + FLOCK_K_SKIP, transcript)
        require(len(point) == height, "invalid native Flock point")
        reductions.append((offset, point, slices))
    verify_native_stack(transcript, layout.private_mu, layout.private_lanes, int(rate.c0), root, private, reductions)
    verify_native_stack(transcript, layout.fixed_mu, layout.fixed_lanes, 1, layout.fixed_root, fixed, [])
    transcript.finish()


def verify_execution(program: ProgramInfo, public_input: Digest, proof: Proof) -> None:
    transcript = Transcript(proof, program.iv(), public_input)
    header = Header.read(transcript)
    layout = Layout.build(program, public_input.value, header)
    root = Digest.from_halves(*transcript.next_scalars(2))
    bus = verify_bus_balance(layout, transcript)
    verify_tables(layout, bus, transcript)
    verify_opening(layout, bus.claims, root, transcript)
    transcript.finish()


def main(argv: Sequence[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Independently verify an RV64IM or field-native circuit proof")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--elf", type=Path, help="exact ELF64LE RISC-V executable")
    mode.add_argument("--native-key", type=Path, help="trusted descriptor: exactly 77 little-endian u64 words")
    parser.add_argument("--public-input", help="RISC mode: 32-byte public input as hexadecimal")
    parser.add_argument("--public-fields", type=Path, help="native mode: consecutive 24-byte little-endian F192 values")
    parser.add_argument("--proof", required=True, type=Path, help="canonical RV64PRF1 proof")
    arguments = parser.parse_args(argv)
    try:
        proof = Proof.load(arguments.proof)
        if arguments.native_key is not None:
            require(
                arguments.public_fields is not None and arguments.public_input is None,
                "native mode requires --public-fields and forbids --public-input",
            )
            key_bytes = arguments.native_key.read_bytes()
            require(len(key_bytes) == 8 * NATIVE_KEY_WORDS, "native key descriptor must be 616 bytes")
            fields = arguments.public_fields.read_bytes()
            require(len(fields) % 24 == 0, "partial native public field")
            verify_native(unpack("<77Q", key_bytes), [E.from_bytes(fields[i : i + 24]) for i in range(0, len(fields), 24)], proof)
        else:
            require(
                arguments.public_input is not None and arguments.public_fields is None,
                "RISC mode requires --public-input and forbids --public-fields",
            )
            public = bytes.fromhex(arguments.public_input)
            require(len(arguments.public_input) == 64 and len(public) == 32, "public input must be exactly 64 hexadecimal digits")
            program = ProgramInfo.from_elf(arguments.elf.read_bytes())
            verify_execution(program, Digest(public), proof)
    except (OSError, ValueError, KeyError, IndexError, VerificationError) as exc:
        parser.exit(1, f"reject: {exc}\n")
    print("accept")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
