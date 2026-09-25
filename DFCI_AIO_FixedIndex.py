#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DFCI AIO Fixed-Index Tool
Dengeki Bunko: Fighting Climax Ignition

Three synchronized tabs:
  1) Font Tool   - writes the 134 Vietnamese glyphs into fixed FNT indices.
  2) Font Editor - displays/edits the same fixed FNT indices.
  3) Replace Tool- converts Vietnamese text to the exact raw code bytes stored
                   at those same FNT indices.

IMPORTANT
---------
The mapping is index-based, NOT vi_mapping.json-based and NOT F040-based.
The first Vietnamese character is always FNT index 95 (display row 96):
    95 -> á
    96 -> à
    ...
    228 -> Ỵ
The FNT code already stored in each target record is preserved by Font Tool.
Replace Tool reads those preserved codes from Font00.fnt and writes those exact
bytes into the translated text.  This keeps all three tabs synchronized.

Requires: Python 3.10+ and Pillow
"""

from __future__ import annotations

import codecs
import gzip
import json
import os
import shutil
import struct
import sys
import traceback
import statistics
import unicodedata
from dataclasses import dataclass
from pathlib import Path
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

try:
    from PIL import Image, ImageDraw, ImageFont, ImageTk
except ImportError:
    raise SystemExit("Pillow is required. Install with: py -m pip install Pillow")

# -----------------------------------------------------------------------------
# Shared fixed-index mapping
# -----------------------------------------------------------------------------

APP_TITLE = "DFCI AIO - Fixed Index v8"
FNT_HEADER_SIZE = 0x3E
GLYPH_RECORD_SIZE = 0x16
GXT_HEADER_SIZE = 0x40
PAGE_W = 512
PAGE_H = 512
PAGE_COUNT = 14            # Font_0000..0013; page 0014 is copied untouched.
FIXED_START_INDEX = 95     # Tree display row 96.

# DO NOT SORT / REORDER.
VI_MAPPING_ORDER = (
    "áàảãạâấầẩẫậăắằẳẵặđéèẻẽẹêếềểễệíìỉĩị"
    "óòỏõọôốồổỗộơớờởỡợúùủũụưứừửữựýỳỷỹỵ"
    "ÁÀẢÃẠÂẤẦẨẪẬĂẮẰẲẴẶĐÉÈẺẼẸÊẾỀỂỄỆÍÌỈĨỊ"
    "ÓÒỎÕỌÔỐỒỔỖỘƠỚỜỞỠỢÚÙỦŨỤƯỨỪỬỮỰÝỲỶỸỴ"
)
FIXED_COUNT = len(VI_MAPPING_ORDER)
FIXED_END_INDEX = FIXED_START_INDEX + FIXED_COUNT - 1
VI_CHAR_TO_INDEX = {c: FIXED_START_INDEX + i for i, c in enumerate(VI_MAPPING_ORDER)}
VI_INDEX_TO_CHAR = {FIXED_START_INDEX + i: c for i, c in enumerate(VI_MAPPING_ORDER)}

TEXT_EXTS = {
    ".txt", ".csv", ".tsv", ".ini", ".cfg", ".conf", ".json", ".xml",
    ".yml", ".yaml", ".lua", ".ks", ".scr", ".script", ".msg", ".mes",
    ".dat", ".lst", ".tbl", ".po", ".srt", ".ass", ".sub"
}


# -----------------------------------------------------------------------------
# Shared FNT / GXT core
# -----------------------------------------------------------------------------

@dataclass
class Glyph:
    code: int
    page: int
    center_x: int
    neg_half_width: int
    neg_top: int
    advance: int
    width: int
    height: int
    atlas_x: int
    atlas_y: int

    @classmethod
    def unpack(cls, raw: bytes, off: int) -> "Glyph":
        return cls(*struct.unpack_from("<I H h h h H H H H H", raw, off))

    def pack(self) -> bytes:
        return struct.pack(
            "<I H h h h H H H H H",
            self.code, self.page, self.center_x, self.neg_half_width,
            self.neg_top, self.advance, self.width, self.height,
            self.atlas_x, self.atlas_y,
        )


def load_fnt(path: Path):
    raw = path.read_bytes()
    if len(raw) < FNT_HEADER_SIZE:
        raise ValueError("Font00.fnt quá nhỏ.")
    count = struct.unpack_from("<I", raw, 0x34)[0]
    expected = FNT_HEADER_SIZE + count * GLYPH_RECORD_SIZE
    if len(raw) < expected:
        raise ValueError(
            f"Font00.fnt bị cắt: header={count} glyph, cần {expected} byte, "
            f"file chỉ có {len(raw)} byte."
        )
    header = bytearray(raw[:FNT_HEADER_SIZE])
    glyphs = [
        Glyph.unpack(raw, FNT_HEADER_SIZE + i * GLYPH_RECORD_SIZE)
        for i in range(count)
    ]
    tail = raw[expected:]
    return header, glyphs, tail


def save_fnt(path: Path, header: bytearray, glyphs: list[Glyph], tail: bytes):
    hdr = bytearray(header)
    struct.pack_into("<I", hdr, 0x34, len(glyphs))
    path.write_bytes(bytes(hdr) + b"".join(g.pack() for g in glyphs) + tail)


def validate_fixed_indices(glyphs: list[Glyph]):
    if len(glyphs) <= FIXED_END_INDEX:
        raise ValueError(
            f"Font chỉ có {len(glyphs)} glyph; fixed map cần ít nhất "
            f"{FIXED_END_INDEX + 1} glyph để dùng FNT #{FIXED_START_INDEX}..#{FIXED_END_INDEX}."
        )


def code_to_raw_bytes(code: int) -> bytes:
    if 0 < code <= 0xFF:
        return bytes([code])
    if 0 < code <= 0xFFFF:
        return bytes([(code >> 8) & 0xFF, code & 0xFF])
    raise ValueError(f"FNT code 0x{code:X} không thể biểu diễn bằng 1/2 byte.")


def decode_fnt_code(code: int) -> str | None:
    try:
        return code_to_raw_bytes(code).decode("cp932")
    except Exception:
        return None


def fixed_index_byte_map(glyphs: list[Glyph]):
    """Return exact fixed-index mapping based on codes already present in FNT.

    char -> raw bytes from glyph record at FIXED_START_INDEX + mapping order.
    No JSON and no F040 assumptions.
    """
    validate_fixed_indices(glyphs)
    out: dict[str, bytes] = {}
    seen: dict[bytes, str] = {}
    rows = []
    for order, char in enumerate(VI_MAPPING_ORDER, 1):
        idx = FIXED_START_INDEX + order - 1
        code = glyphs[idx].code
        raw = code_to_raw_bytes(code)
        if raw in seen:
            raise ValueError(
                f"Fixed-index map bị trùng code: {seen[raw]!r} và {char!r} cùng dùng "
                f"{raw.hex(' ').upper()}. Không thể replace text an toàn."
            )
        seen[raw] = char
        out[char] = raw
        rows.append((order, idx, char, code, raw, decode_fnt_code(code)))
    return out, rows


# Morton swizzle ---------------------------------------------------------------

_MORTON = None


def part1by1(n: int) -> int:
    n &= 0xFFFF
    n = (n | (n << 8)) & 0x00FF00FF
    n = (n | (n << 4)) & 0x0F0F0F0F
    n = (n | (n << 2)) & 0x33333333
    n = (n | (n << 1)) & 0x55555555
    return n


def morton_table():
    global _MORTON
    if _MORTON is None:
        tab = [0] * (PAGE_W * PAGE_H)
        k = 0
        for y in range(PAGE_H):
            yy = part1by1(y)
            for x in range(PAGE_W):
                tab[k] = yy | (part1by1(x) << 1)
                k += 1
        _MORTON = tab
    return _MORTON


def read_gxt(path: Path):
    """Return (prefix, linear RGBA, suffix), preserving non-texture bytes."""
    with gzip.open(path, "rb") as f:
        raw = f.read()
    if len(raw) < GXT_HEADER_SIZE or raw[:4] != b"GXT\x00":
        raise ValueError(f"{path.name}: không phải GXT hợp lệ.")

    data_offset = struct.unpack_from("<I", raw, 0x0C)[0]
    data_size = struct.unpack_from("<I", raw, 0x10)[0]
    width, height = struct.unpack_from("<HH", raw, 0x38)

    expected = PAGE_W * PAGE_H * 4
    if (width, height) != (PAGE_W, PAGE_H):
        raise ValueError(f"{path.name}: kích thước {width}x{height}, cần 512x512.")
    if data_size != expected:
        raise ValueError(
            f"{path.name}: dataSize=0x{data_size:X}, cần 0x{expected:X} cho RGBA8888."
        )
    if data_offset < GXT_HEADER_SIZE or data_offset + data_size > len(raw):
        raise ValueError(
            f"{path.name}: vùng texture không hợp lệ "
            f"(offset=0x{data_offset:X}, size=0x{data_size:X})."
        )

    payload = raw[data_offset:data_offset + data_size]
    linear = bytearray(data_size)
    tab = morton_table()
    for linear_pixel, morton_pixel in enumerate(tab):
        src = morton_pixel * 4
        dst = linear_pixel * 4
        linear[dst:dst + 4] = payload[src:src + 4]

    return bytearray(raw[:data_offset]), linear, bytes(raw[data_offset + data_size:])


def write_gxt(path: Path, prefix: bytearray, linear: bytearray, suffix: bytes = b""):
    expected = PAGE_W * PAGE_H * 4
    if len(linear) != expected:
        raise ValueError(f"RGBA buffer sai: {len(linear)} byte, cần {expected}.")
    payload = bytearray(expected)
    tab = morton_table()
    for linear_pixel, morton_pixel in enumerate(tab):
        src = linear_pixel * 4
        dst = morton_pixel * 4
        payload[dst:dst + 4] = linear[src:src + 4]
    with open(path, "wb") as fh:
        with gzip.GzipFile(filename="", mode="wb", fileobj=fh, mtime=0) as gz:
            gz.write(bytes(prefix) + bytes(payload) + bytes(suffix))


# Atlas helpers ----------------------------------------------------------------

def build_occupancy(glyphs: list[Glyph], padding: int, exclude_indices: set[int] | None = None):
    exclude_indices = exclude_indices or set()
    occ = [bytearray(PAGE_W * PAGE_H) for _ in range(PAGE_COUNT)]
    for idx, g in enumerate(glyphs):
        if idx in exclude_indices:
            continue
        if not (0 <= g.page < PAGE_COUNT) or g.width <= 0 or g.height <= 0:
            continue
        x0 = max(0, g.atlas_x - padding)
        y0 = max(0, g.atlas_y - padding)
        x1 = min(PAGE_W, g.atlas_x + g.width + padding)
        y1 = min(PAGE_H, g.atlas_y + g.height + padding)
        o = occ[g.page]
        for y in range(y0, y1):
            start = y * PAGE_W + x0
            o[start:start + (x1 - x0)] = b"\x01" * (x1 - x0)
    return occ


def rect_is_free(o: bytearray, x: int, y: int, w: int, h: int, padding: int) -> bool:
    x0 = max(0, x - padding)
    y0 = max(0, y - padding)
    x1 = min(PAGE_W, x + w + padding)
    y1 = min(PAGE_H, y + h + padding)
    for yy in range(y0, y1):
        if any(o[yy * PAGE_W + x0: yy * PAGE_W + x1]):
            return False
    return True


def mark_rect(o: bytearray, x: int, y: int, w: int, h: int, padding: int):
    x0 = max(0, x - padding)
    y0 = max(0, y - padding)
    x1 = min(PAGE_W, x + w + padding)
    y1 = min(PAGE_H, y + h + padding)
    for yy in range(y0, y1):
        start = yy * PAGE_W + x0
        o[start:start + (x1 - x0)] = b"\x01" * (x1 - x0)


def find_space(occ, w: int, h: int, padding: int):
    page_order = [13] + list(range(12, -1, -1))
    for page in page_order:
        o = occ[page]
        for y in range(padding, PAGE_H - h - padding + 1):
            for x in range(padding, PAGE_W - w - padding + 1):
                if rect_is_free(o, x, y, w, h, padding):
                    mark_rect(o, x, y, w, h, padding)
                    return page, x, y
    return None


DOT_BELOW_CHARS = set("ạậặẹệịọộợụựỵẠẬẶẸỆỊỌỘỢỤỰỴ")


def base_latin_char(char: str) -> str:
    """Return the unaccented Latin base used to match stock FNT metrics."""
    if char == "đ":
        return "d"
    if char == "Đ":
        return "D"
    decomp = unicodedata.normalize("NFD", char)
    for c in decomp:
        if "A" <= c <= "Z" or "a" <= c <= "z":
            return c
    return char


# Vietnamese letters carrying the below-dot mark.  The value is the same
# letter shape with ONLY the below-dot removed.  This lets the builder keep
# the body/accent top where it belongs while allowing the dot to extend below.
DOT_BELOW_REFERENCE = {
    "ạ": "a", "ậ": "â", "ặ": "ă",
    "ẹ": "e", "ệ": "ê",
    "ị": "i",
    "ọ": "o", "ộ": "ô", "ợ": "ơ",
    "ụ": "u", "ự": "ư",
    "ỵ": "y",
    "Ạ": "A", "Ậ": "Â", "Ặ": "Ă",
    "Ẹ": "E", "Ệ": "Ê",
    "Ị": "I",
    "Ọ": "O", "Ộ": "Ô", "Ợ": "Ơ",
    "Ụ": "U", "Ự": "Ư",
    "Ỵ": "Y",
}


def _ttf_render_top(font_path: Path, char: str, font_size: int, baseline: int) -> int:
    """Return the cropped glyph top, in the same coordinate system as FNT neg_top."""
    font = ImageFont.truetype(str(font_path), font_size)
    probe = Image.new("L", (192, 192), 0)
    draw = ImageDraw.Draw(probe)
    bbox = draw.textbbox((0, 0), char, font=font, anchor="ls")
    if bbox is None:
        raise ValueError(f"TTF không có glyph cho {char!r}.")
    l, t, r, b = bbox
    w0, h0 = max(1, r-l), max(1, b-t)
    img = Image.new("L", (w0, h0), 0)
    d = ImageDraw.Draw(img)
    d.text((-l, -t), char, font=font, fill=255, anchor="ls")
    baseline_in_crop = -t
    bb = img.getbbox()
    if bb:
        _, top_trim, _, _ = bb
        baseline_in_crop -= top_trim
    return baseline - baseline_in_crop


def auto_all_negtop(font_path: Path, char: str, font_size: int, baseline: int,
                    ascii_metrics: dict[str, Glyph]) -> int:
    """Infer Neg Top for every Vietnamese glyph from the stock Latin body.

    The stock ASCII letter supplies the game's vertical anchor.  The selected
    TTF supplies only the relative accent/diacritic displacement.  This keeps
    the body of á/à/ả/ã/â/ă/... aligned with stock ``a`` while still allowing
    each accent to occupy its natural space.  The same rule applies to every
    one of the 134 fixed-map characters, upper and lower case.

    For below-dot letters, the dot remains part of the bitmap height and is
    allowed to extend below the nominal cell rather than pushing the whole
    body upward.
    """
    base = base_latin_char(char)
    stock = ascii_metrics.get(base)
    ttf_base_top = _ttf_render_top(font_path, base, font_size, baseline)
    ttf_char_top = _ttf_render_top(font_path, char, font_size, baseline)

    # Anchor the unaccented body to the game's own ASCII metric whenever
    # possible.  Accent positioning comes from the TTF as a relative delta.
    base_top = -stock.neg_top if stock is not None else ttf_base_top
    accent_delta = ttf_char_top - ttf_base_top
    return int(round(base_top + accent_delta))


def stock_ascii_metrics(glyphs: list[Glyph]) -> dict[str, Glyph]:
    out = {}
    for g in glyphs:
        c = decode_fnt_code(g.code)
        if c and len(c) == 1 and ord(c) < 128 and c not in out:
            out[c] = g
    return out


def auto_fit_font_metrics(font_path: Path, glyphs: list[Glyph], min_size: int = 8, max_size: int = 40):
    """Estimate TTF size/baseline from the game's stock ASCII metrics.

    The old builder fitted every accented glyph into 11x22 as a whole.  That can
    shrink the letter body merely because an accent/dot extends the bbox.  Here
    we first match the TTF's *unaccented* A-Z/a-z body to the stock FNT and only
    then render Vietnamese at that same scale.
    """
    refs = stock_ascii_metrics(glyphs)
    sample = [c for c in "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789" if c in refs]
    if not sample:
        raise ValueError("Không tìm thấy ASCII metrics trong Font00.fnt để Auto-fit.")

    probe = Image.new("L", (192, 192), 0)
    draw = ImageDraw.Draw(probe)
    best = None
    for size in range(min_size, max_size + 1):
        font = ImageFont.truetype(str(font_path), size)
        errs = []
        for c in sample:
            bbox = draw.textbbox((0, 0), c, font=font, anchor="ls")
            if not bbox:
                continue
            l, t, r, b = bbox
            rw, rh = max(1, r-l), max(1, b-t)
            ref = refs[c]
            # Height is more important than width for matching the original body.
            errs.append(abs(rh-ref.height) + 0.35*abs(rw-ref.width))
        if not errs:
            continue
        score = statistics.median(errs)
        if best is None or score < best[0]:
            best = (score, size)
    if best is None:
        raise ValueError("Không Auto-fit được TTF/OTF này.")

    _, size = best
    font = ImageFont.truetype(str(font_path), size)
    baseline_candidates = []
    for c in sample:
        bbox = draw.textbbox((0, 0), c, font=font, anchor="ls")
        if not bbox:
            continue
        _, t, _, _ = bbox
        ref = refs[c]
        stock_top = -ref.neg_top
        baseline_candidates.append(stock_top - t)

    baseline = int(round(statistics.median(baseline_candidates))) if baseline_candidates else 19
    # Stock Latin occupies a 22px-high cell in this font format.
    cell_height = max(22, max((-refs[c].neg_top + refs[c].height) for c in sample))
    advance = int(round(statistics.median([refs[c].advance for c in sample])))
    return size, baseline, cell_height, advance, best[0]


def render_glyph(font_path: Path, char: str, font_size: int, baseline: int,
                 cell_height: int, advance: int, *, forced_top: int | None = None,
                 allow_below: bool = False):
    """Render at the chosen body scale while preserving Vietnamese marks.

    ``forced_top`` can anchor any Vietnamese glyph to the stock Latin body
    metrics.  For below-dot glyphs, ``allow_below`` additionally lets the dot
    extend beneath the nominal cell instead of moving the whole character
    upward.  The returned ``top`` becomes -neg_top.
    """
    font = ImageFont.truetype(str(font_path), font_size)
    probe = Image.new("L", (192, 192), 0)
    draw = ImageDraw.Draw(probe)
    bbox = draw.textbbox((0, 0), char, font=font, anchor="ls")
    if bbox is None:
        raise ValueError(f"TTF không có glyph cho {char!r}.")
    l, t, r, b = bbox
    w0, h0 = max(1, r-l), max(1, b-t)

    img = Image.new("L", (w0, h0), 0)
    d = ImageDraw.Draw(img)
    d.text((-l, -t), char, font=font, fill=255, anchor="ls")
    baseline_in_crop = -t

    bb = img.getbbox()
    if bb:
        left_trim, top_trim, _, _ = bb
        img = img.crop(bb)
        baseline_in_crop -= top_trim

    w, h = img.size

    # Preserve vertical size.  Horns/accents may make a glyph wider than the
    # stock cell; compress X only rather than shrinking the entire character.
    if w > advance:
        img = img.resize((max(1, advance), h), Image.Resampling.LANCZOS)
        w, h = img.size

    # A below-dot glyph is intentionally allowed to grow below the nominal
    # 22px cell.  Scaling it to cell_height is exactly what made the body small
    # and/or shifted upward in older builds.
    if not allow_below and h > cell_height:
        ratio = cell_height / h
        nw = max(1, min(advance, round(w * ratio)))
        img = img.resize((nw, cell_height), Image.Resampling.LANCZOS)
        baseline_in_crop = round(baseline_in_crop * ratio)
        w, h = img.size

    natural_top = baseline - baseline_in_crop
    top = forced_top if forced_top is not None else natural_top
    if top < 0:
        top = 0

    if not allow_below and top + h > cell_height:
        # Normal glyphs keep the old cell guard.
        top = max(0, cell_height - h)

    return img, int(top)


def paint_glyph(linear: bytearray, alpha_img: Image.Image, x: int, y: int):
    pix = alpha_img.tobytes()
    w, h = alpha_img.size
    for yy in range(h):
        for xx in range(w):
            a = pix[yy * w + xx]
            dst = ((y + yy) * PAGE_W + (x + xx)) * 4
            linear[dst + 0] = 255
            linear[dst + 1] = 255
            linear[dst + 2] = 255
            linear[dst + 3] = a


def glyph_alpha_from_page(linear: bytearray, g: Glyph):
    img = Image.new("L", (g.width, g.height), 0)
    pix = img.load()
    for y in range(g.height):
        for x in range(g.width):
            off = ((g.atlas_y + y) * PAGE_W + (g.atlas_x + x)) * 4
            pix[x, y] = linear[off + 3]
    return img


def paint_alpha(linear: bytearray, g: Glyph, img: Image.Image):
    if img.mode != "L":
        img = img.convert("L")
    if img.size != (g.width, g.height):
        img = img.resize((g.width, g.height), Image.Resampling.LANCZOS)
    pix = img.load()
    for y in range(g.height):
        for x in range(g.width):
            off = ((g.atlas_y + y) * PAGE_W + (g.atlas_x + x)) * 4
            linear[off:off + 4] = bytes((255, 255, 255, pix[x, y]))


def clear_glyph_rect(linear: bytearray, g: Glyph):
    if not (0 <= g.page < PAGE_COUNT) or g.width <= 0 or g.height <= 0:
        return
    for y in range(g.height):
        for x in range(g.width):
            px = g.atlas_x + x
            py = g.atlas_y + y
            if 0 <= px < PAGE_W and 0 <= py < PAGE_H:
                off = (py * PAGE_W + px) * 4
                linear[off:off + 4] = bytes((255, 255, 255, 0))


def image_to_glyph_alpha(img: Image.Image) -> Image.Image:
    """Convert an imported PNG to the atlas alpha bitmap without flattening transparency."""
    if img.mode == "L":
        return img.copy()
    if "A" in img.getbands():
        alpha = img.getchannel("A")
        lo, hi = alpha.getextrema()
        if lo != 255 or hi != 255:
            return alpha
    return img.convert("L")


# Text helpers -----------------------------------------------------------------

def looks_binary(raw: bytes):
    if raw.startswith((
        codecs.BOM_UTF8,
        codecs.BOM_UTF16_LE, codecs.BOM_UTF16_BE,
        codecs.BOM_UTF32_LE, codecs.BOM_UTF32_BE,
    )):
        return False
    if b"\x00" in raw[:4096]:
        return True
    sample = raw[:8192]
    if not sample:
        return False
    bad = sum(1 for b in sample if b < 32 and b not in (9, 10, 13, 12))
    return bad / len(sample) > 0.03


def decode_text(raw: bytes, ext: str):
    """Decode text-like files, with explicit CSV/TSV handling.

    CSV exported by Excel is commonly UTF-8 BOM or UTF-16LE.  Some UTF-16 CSVs
    have no BOM, so detect their NUL-byte pattern before generic binary checks.
    Vietnamese legacy CSV may also be CP1258; accept that as a final fallback.
    """
    ext = ext.lower()
    is_table = ext in {".csv", ".tsv"}

    if raw.startswith(codecs.BOM_UTF8):
        return raw[3:].decode("utf-8"), "utf-8-sig"
    if raw.startswith(codecs.BOM_UTF16_LE):
        return raw[2:].decode("utf-16-le"), "utf-16-le"
    if raw.startswith(codecs.BOM_UTF16_BE):
        return raw[2:].decode("utf-16-be"), "utf-16-be"
    if raw.startswith(codecs.BOM_UTF32_LE):
        return raw[4:].decode("utf-32-le"), "utf-32-le"
    if raw.startswith(codecs.BOM_UTF32_BE):
        return raw[4:].decode("utf-32-be"), "utf-32-be"

    # Excel/LibreOffice CSV/TSV can be UTF-16 without a BOM.  Detect the
    # alternating NUL pattern before looks_binary() rejects it.
    if is_table and raw:
        probe = raw[:4096]
        even_nuls = sum(1 for i in range(0, len(probe), 2) if probe[i] == 0)
        odd_nuls = sum(1 for i in range(1, len(probe), 2) if probe[i] == 0)
        even_slots = max(1, (len(probe) + 1) // 2)
        odd_slots = max(1, len(probe) // 2)
        try:
            if odd_nuls / odd_slots > 0.25 and even_nuls / even_slots < 0.10:
                return raw.decode("utf-16-le"), "utf-16-le(no-bom)"
            if even_nuls / even_slots > 0.25 and odd_nuls / odd_slots < 0.10:
                return raw.decode("utf-16-be"), "utf-16-be(no-bom)"
        except UnicodeDecodeError:
            pass

    if looks_binary(raw):
        return None

    try:
        return raw.decode("utf-8"), "utf-8"
    except UnicodeDecodeError:
        pass

    try:
        txt = raw.decode("cp932")
        if ext not in TEXT_EXTS:
            probe = txt[:8192]
            if probe:
                bad = sum(1 for c in probe if ord(c) < 32 and c not in "\t\r\n\f")
                if bad / len(probe) > 0.01:
                    return None
        return txt, "cp932"
    except UnicodeDecodeError:
        pass

    # Legacy Vietnamese spreadsheet export fallback.
    if is_table:
        try:
            return raw.decode("cp1258"), "cp1258"
        except UnicodeDecodeError:
            pass

    return None


class FixedTextEncodeError(Exception):
    def __init__(self, char: str, position: int):
        self.char = char
        self.position = position
        super().__init__(
            f"Ký tự {char!r} tại vị trí {position} không có trong CP932 và không thuộc fixed map."
        )


def encode_fixed_index_cp932(text: str, char_to_bytes: dict[str, bytes]):
    """Encode text to CP932 while writing mapped Vietnamese chars as exact FNT bytes."""
    out = bytearray()
    replaced = 0
    for pos, c in enumerate(text):
        raw = char_to_bytes.get(c)
        if raw is not None:
            out.extend(raw)
            replaced += 1
            continue
        try:
            out.extend(c.encode("cp932"))
        except UnicodeEncodeError as e:
            raise FixedTextEncodeError(c, pos) from e
    return bytes(out), replaced


# -----------------------------------------------------------------------------
# Reusable UI helpers
# -----------------------------------------------------------------------------

def add_path_row(parent, row, label, variable, command, button_text="Chọn…"):
    ttk.Label(parent, text=label, width=18).grid(row=row, column=0, sticky="w", pady=4)
    ttk.Entry(parent, textvariable=variable).grid(row=row, column=1, sticky="ew", padx=6)
    ttk.Button(parent, text=button_text, command=command).grid(row=row, column=2)
    parent.grid_columnconfigure(1, weight=1)


class LogBox(tk.Text):
    def __init__(self, parent, **kw):
        super().__init__(parent, state="disabled", wrap="word", **kw)

    def clear(self):
        self.configure(state="normal")
        self.delete("1.0", "end")
        self.configure(state="disabled")

    def write_line(self, s=""):
        self.configure(state="normal")
        self.insert("end", s + "\n")
        self.see("end")
        self.configure(state="disabled")
        self.update_idletasks()


# -----------------------------------------------------------------------------
# Tab 1 - Font Tool (fixed-index writer)
# -----------------------------------------------------------------------------

class FontToolTab(ttk.Frame):
    def __init__(self, parent, aio):
        super().__init__(parent, padding=10)
        self.aio = aio
        self.src_var = tk.StringVar()
        self.ttf_var = tk.StringVar()
        self.out_var = tk.StringVar()
        self.size_var = tk.IntVar(value=22)
        self.baseline_var = tk.IntVar(value=19)
        self.cellh_var = tk.IntVar(value=22)
        self.advance_var = tk.IntVar(value=11)
        self.padding_var = tk.IntVar(value=1)
        self.auto_fit_var = tk.BooleanVar(value=True)
        self.auto_all_negtop_var = tk.BooleanVar(value=True)
        self.build_ui()

    def build_ui(self):
        files = ttk.LabelFrame(self, text="Input / Output", padding=10)
        files.pack(fill="x")
        add_path_row(files, 0, "Font folder:", self.src_var, self.choose_src)
        add_path_row(files, 1, "TTF / OTF:", self.ttf_var, self.choose_ttf)
        add_path_row(files, 2, "Output folder:", self.out_var, self.choose_out)

        opts = ttk.LabelFrame(self, text="Font build settings", padding=10)
        opts.pack(fill="x", pady=(10, 0))
        fields = [
            ("TTF size", self.size_var),
            ("Baseline", self.baseline_var),
            ("Cell height", self.cellh_var),
            ("Advance", self.advance_var),
            ("Atlas padding", self.padding_var),
        ]
        for col, (name, var) in enumerate(fields):
            ttk.Label(opts, text=name + ":").grid(row=0, column=col * 2, sticky="e", padx=(6, 2), pady=4)
            ttk.Spinbox(opts, from_=0, to=64, textvariable=var, width=6).grid(row=0, column=col * 2 + 1, sticky="w", padx=(0, 10))
        ttk.Checkbutton(
            opts, text="Auto-fit size/baseline theo Latin gốc", variable=self.auto_fit_var
        ).grid(row=1, column=0, columnspan=4, sticky="w", padx=6, pady=(4, 0))
        ttk.Checkbutton(
            opts, text="Auto Neg Top toàn bộ 134 chữ Việt", variable=self.auto_all_negtop_var
        ).grid(row=1, column=4, columnspan=4, sticky="w", padx=6, pady=(4, 0))
        ttk.Button(opts, text="Đo size gốc ngay", command=self.measure_original_metrics).grid(
            row=1, column=8, columnspan=2, sticky="w", padx=6, pady=(4, 0)
        )

        mapbox = ttk.LabelFrame(self, text="Built-in fixed-index map", padding=10)
        mapbox.pack(fill="x", pady=(10, 0))
        ttk.Label(
            mapbox,
            text=(
                f"FNT #{FIXED_START_INDEX} (row {FIXED_START_INDEX + 1}) = á  →  "
                f"FNT #{FIXED_END_INDEX} = Ỵ.  "
                "Font Tool giữ nguyên code của từng FNT record; chỉ thay bitmap/metrics."
            ),
            wraplength=1050,
        ).pack(anchor="w")
        fixed = tk.Text(mapbox, height=3, wrap="char")
        fixed.pack(fill="x", pady=(6, 0))
        fixed.insert("1.0", VI_MAPPING_ORDER)
        fixed.configure(state="disabled")

        actions = ttk.Frame(self)
        actions.pack(fill="x", pady=10)
        ttk.Button(actions, text="Analyze fixed indices", command=self.analyze).pack(side="left")
        ttk.Button(actions, text="Build font", command=self.build_font).pack(side="left", padx=8)
        ttk.Button(actions, text="Dùng output cho Editor + Replace", command=self.use_output_everywhere).pack(side="left")

        logframe = ttk.LabelFrame(self, text="Log", padding=8)
        logframe.pack(fill="both", expand=True)
        self.log = LogBox(logframe, height=18)
        ys = ttk.Scrollbar(logframe, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=ys.set)
        self.log.pack(side="left", fill="both", expand=True)
        ys.pack(side="right", fill="y")

    def choose_src(self):
        p = filedialog.askdirectory(title="Folder chứa Font00.fnt + Font_0000..0013.gxt.gz")
        if p:
            self.src_var.set(p)
            if not self.out_var.get():
                src = Path(p)
                self.out_var.set(str(src.parent / (src.name + "_VI")))

    def choose_ttf(self):
        p = filedialog.askopenfilename(
            title="Chọn TTF/OTF",
            filetypes=[("TrueType / OpenType", "*.ttf *.otf"), ("All files", "*.*")],
        )
        if p:
            self.ttf_var.set(p)

    def choose_out(self):
        p = filedialog.askdirectory(title="Chọn output folder")
        if p:
            self.out_var.set(p)

    def use_output_everywhere(self):
        p = self.out_var.get().strip()
        if p:
            self.aio.editor_tab.folder_var.set(p)
            self.aio.replace_tab.font_var.set(p)

    def validate_inputs(self, need_ttf=True):
        src = Path(self.src_var.get())
        if not src.is_dir():
            raise ValueError("Chưa chọn source font folder hợp lệ.")
        if not (src / "Font00.fnt").is_file():
            raise ValueError("Thiếu Font00.fnt.")
        for p in range(PAGE_COUNT):
            fn = src / f"Font_{p:04d}.gxt.gz"
            if not fn.is_file():
                raise ValueError(f"Thiếu {fn.name}.")
        ttf = Path(self.ttf_var.get())
        if need_ttf and not ttf.is_file():
            raise ValueError("Chưa chọn TTF/OTF.")
        return src, ttf

    def measure_original_metrics(self):
        try:
            src, ttf = self.validate_inputs(need_ttf=True)
            _, glyphs, _ = load_fnt(src / "Font00.fnt")
            size, baseline, cell_h, advance, score = auto_fit_font_metrics(ttf, glyphs)
            self.size_var.set(size)
            self.baseline_var.set(baseline)
            self.cellh_var.set(cell_h)
            self.advance_var.set(advance)
            self.log.write_line(
                f"Auto-fit: TTF size={size}, baseline={baseline}, cell={cell_h}, advance={advance}, score={score:.2f}"
            )
        except Exception as e:
            messagebox.showerror("Auto-fit", str(e))

    def analyze(self):
        try:
            self.log.clear()
            src, _ = self.validate_inputs(need_ttf=False)
            header, glyphs, tail = load_fnt(src / "Font00.fnt")
            validate_fixed_indices(glyphs)
            _, rows = fixed_index_byte_map(glyphs)
            self.log.write_line(f"Glyph records: {len(glyphs)}")
            self.log.write_line(f"Fixed block: FNT #{FIXED_START_INDEX}..#{FIXED_END_INDEX} ({FIXED_COUNT} glyphs)")
            self.log.write_line(f"Atlas count in header: {struct.unpack_from('<H', header, 0x38)[0]}")
            self.log.write_line("")
            self.log.write_line("First 12 fixed mappings from this FNT:")
            for order, idx, char, code, raw, placeholder in rows[:12]:
                self.log.write_line(
                    f"{order:03d}. FNT #{idx:04d}  {char}  code=0x{code:04X}  "
                    f"bytes={raw.hex(' ').upper()}  cp932={placeholder!r}"
                )
            self.log.write_line("...")
            for order, idx, char, code, raw, placeholder in rows[-3:]:
                self.log.write_line(
                    f"{order:03d}. FNT #{idx:04d}  {char}  code=0x{code:04X}  "
                    f"bytes={raw.hex(' ').upper()}  cp932={placeholder!r}"
                )
            self.log.write_line("")
            self.log.write_line("OK: fixed-index codes are unique and usable by Replace Tool.")
        except Exception as e:
            messagebox.showerror("Analyze failed", str(e))
            self.log.write_line("")
            self.log.write_line(traceback.format_exc())

    def build_font(self):
        try:
            src, ttf = self.validate_inputs(need_ttf=True)
            out_text = self.out_var.get().strip()
            if not out_text:
                raise ValueError("Chưa chọn output folder.")
            out = Path(out_text)
            if src.resolve() == out.resolve():
                raise ValueError("Output folder phải khác source folder.")

            font_size = int(self.size_var.get())
            baseline = int(self.baseline_var.get())
            cell_h = int(self.cellh_var.get())
            advance = int(self.advance_var.get())
            padding = int(self.padding_var.get())
            if font_size <= 0 or cell_h <= 0 or advance <= 0:
                raise ValueError("Font size, cell height và advance phải > 0.")
            if not (0 <= baseline <= cell_h):
                raise ValueError("Baseline phải nằm trong cell height.")
            if not (0 <= padding <= 4):
                raise ValueError("Atlas padding nên nằm trong 0..4.")

            self.log.clear()
            self.log.write_line("Loading Font00.fnt…")
            header, glyphs, tail = load_fnt(src / "Font00.fnt")
            validate_fixed_indices(glyphs)
            _, before_rows = fixed_index_byte_map(glyphs)  # also validates unique codes

            if self.auto_fit_var.get():
                font_size, baseline, cell_h, advance, fit_score = auto_fit_font_metrics(ttf, glyphs)
                self.size_var.set(font_size)
                self.baseline_var.set(baseline)
                self.cellh_var.set(cell_h)
                self.advance_var.set(advance)
                self.log.write_line(
                    f"Auto-fit Latin gốc: size={font_size}, baseline={baseline}, cell={cell_h}, advance={advance}, score={fit_score:.2f}"
                )

            ascii_metrics = stock_ascii_metrics(glyphs)
            if self.auto_all_negtop_var.get():
                self.log.write_line(
                    f"Auto Neg Top toàn bộ: ON ({FIXED_COUNT} ký tự); "
                    "mỗi glyph neo thân theo Latin gốc, độ lệch dấu lấy từ TTF."
                )
                self.log.write_line(
                    f"Dấu nặng: {len(DOT_BELOW_REFERENCE)} ký tự được phép kéo bitmap xuống dưới cell thay vì đẩy thân chữ lên."
                )

            self.log.write_line(
                f"Fixed-index mode: FNT #{FIXED_START_INDEX}..#{FIXED_END_INDEX}; "
                "code của record được giữ nguyên."
            )
            self.log.write_line("Loading atlas pages 0000..0013…")
            pages = {}
            for p in range(PAGE_COUNT):
                pages[p] = list(read_gxt(src / f"Font_{p:04d}.gxt.gz"))

            target_indices = set(range(FIXED_START_INDEX, FIXED_END_INDEX + 1))
            occ = build_occupancy(glyphs, padding, exclude_indices=target_indices)
            dirty_pages = set()

            for order, char in enumerate(VI_MAPPING_ORDER, 1):
                fnt_idx = FIXED_START_INDEX + order - 1
                old = glyphs[fnt_idx]
                preserved_code = old.code

                base = base_latin_char(char)
                ref = ascii_metrics.get(base)
                char_advance = ref.advance if ref is not None and ref.advance > 0 else advance

                is_dot_below = char in DOT_BELOW_REFERENCE
                forced_top = None
                if self.auto_all_negtop_var.get():
                    forced_top = auto_all_negtop(
                        ttf, char, font_size, baseline, ascii_metrics
                    )

                alpha, top = render_glyph(
                    ttf, char, font_size, baseline, cell_h, char_advance,
                    forced_top=forced_top,
                    allow_below=(is_dot_below and self.auto_all_negtop_var.get()),
                )
                w, h = alpha.size
                pos = find_space(occ, w, h, padding)
                if pos is None:
                    raise RuntimeError(
                        f"Không còn vùng trống atlas cho {char!r} ({w}x{h}). "
                        "Source không bị ghi đè."
                    )
                page, ax, ay = pos
                paint_glyph(pages[page][1], alpha, ax, ay)
                dirty_pages.add(page)

                left = max(0, (char_advance - w) // 2)
                glyphs[fnt_idx] = Glyph(
                    code=preserved_code,
                    page=page,
                    center_x=left + (w // 2),
                    neg_half_width=-(w // 2),
                    neg_top=-top,
                    advance=char_advance,
                    width=w,
                    height=h,
                    atlas_x=ax,
                    atlas_y=ay,
                )
                raw = code_to_raw_bytes(preserved_code)
                auto_note = ""
                if self.auto_all_negtop_var.get():
                    auto_note = f" autoNegTop={-top}"
                    if is_dot_below:
                        overflow = max(0, top + h - cell_h)
                        auto_note += f" below+{overflow}px"
                self.log.write_line(
                    f"[{order:03d}/{FIXED_COUNT}] FNT #{fnt_idx:04d}  {char}  "
                    f"code=0x{preserved_code:04X} [{raw.hex(' ').upper()}]  "
                    f"page {page:02d} ({ax},{ay}) {w}x{h} adv={char_advance} top={top}"
                    f" negTop={-top}{auto_note}"
                )

            out.mkdir(parents=True, exist_ok=True)
            for item in src.iterdir():
                if item.is_file():
                    shutil.copy2(item, out / item.name)

            for p in sorted(dirty_pages):
                write_gxt(
                    out / f"Font_{p:04d}.gxt.gz",
                    pages[p][0], pages[p][1], pages[p][2],
                )
            save_fnt(out / "Font00.fnt", header, glyphs, tail)

            # Audit table only; tools never read it.
            _, rows = fixed_index_byte_map(glyphs)
            with open(out / "dfci_fixed_index_map.tsv", "w", encoding="utf-8", newline="\n") as f:
                f.write("order\tfnt_index\tdisplay_row\tchar\tunicode\tfnt_code\traw_bytes\tcp932_placeholder\n")
                for order, idx, char, code, raw, placeholder in rows:
                    f.write(
                        f"{order}\t{idx}\t{idx+1}\t{char}\tU+{ord(char):04X}\t0x{code:04X}\t"
                        f"{raw.hex(' ').upper()}\t{placeholder or ''}\n"
                    )

            self.log.write_line("")
            self.log.write_line(f"Done. Replaced exactly {FIXED_COUNT} fixed FNT records; glyph count unchanged: {len(glyphs)}.")
            self.log.write_line(f"Dirty pages: {', '.join(f'{p:04d}' for p in sorted(dirty_pages))}")
            self.log.write_line(f"Output: {out}")
            self.log.write_line("Không tạo/đọc vi_mapping.json.")

            self.aio.editor_tab.folder_var.set(str(out))
            self.aio.replace_tab.font_var.set(str(out))
            messagebox.showinfo(
                "Build complete",
                f"Đã ghi {FIXED_COUNT} glyph Việt vào FNT #{FIXED_START_INDEX}..#{FIXED_END_INDEX}.\n"
                f"FNT code được giữ nguyên theo từng index.\n\nOutput:\n{out}",
            )
        except Exception as e:
            messagebox.showerror("Build failed", str(e))
            self.log.write_line("")
            self.log.write_line("ERROR:")
            self.log.write_line(traceback.format_exc())


# -----------------------------------------------------------------------------
# Tab 2 - Font Editor (same fixed indices)
# -----------------------------------------------------------------------------

class FontEditorTab(ttk.Frame):
    def __init__(self, parent, aio):
        super().__init__(parent, padding=10)
        self.aio = aio
        self.folder_var = tk.StringVar()
        self.search_var = tk.StringVar()
        self.status_var = tk.StringVar(value="Chọn font folder.")
        self.show_vi_var = tk.BooleanVar(value=True)

        self.header = None
        self.glyphs: list[Glyph] = []
        self.tail = b""
        self.pages = {}
        self.selected_index = None
        self.preview_tk = None
        self.glyph_clipboard = None

        # Every field stored in one FNT glyph record is editable from the UI.
        self.code_edit = tk.StringVar(value="0x0000")
        self.page_edit = tk.IntVar(value=0)
        self.x_edit = tk.IntVar(value=0)
        self.y_edit = tk.IntVar(value=0)
        self.width_edit = tk.IntVar(value=1)
        self.height_edit = tk.IntVar(value=1)
        self.advance_edit = tk.IntVar(value=11)
        self.centerx_edit = tk.IntVar(value=0)
        self.neghalf_edit = tk.IntVar(value=0)
        self.negtop_edit = tk.IntVar(value=0)
        self.build_ui()

    def build_ui(self):
        top = ttk.Frame(self)
        top.pack(fill="x")
        ttk.Label(top, text="Font folder:").pack(side="left")
        ttk.Entry(top, textvariable=self.folder_var).pack(side="left", fill="x", expand=True, padx=6)
        ttk.Button(top, text="Mở…", command=self.choose_folder).pack(side="left")
        ttk.Button(top, text="Load", command=self.load_font).pack(side="left", padx=(6, 0))

        act = ttk.Frame(self, padding=(0, 8, 0, 8))
        act.pack(fill="x")
        ttk.Button(act, text="Export Font", command=self.export_font).pack(side="left")
        ttk.Button(act, text="Import Font", command=self.import_font).pack(side="left", padx=6)
        ttk.Button(act, text="Save current edits…", command=self.save_current).pack(side="left")
        ttk.Button(act, text="Export glyph", command=self.export_selected).pack(side="left", padx=(6, 0))
        ttk.Button(act, text="Import glyph", command=self.import_selected).pack(side="left", padx=(6, 0))
        ttk.Button(act, text="Copy glyph", command=self.copy_glyph).pack(side="left", padx=(6, 0))
        ttk.Button(act, text="Paste glyph", command=self.paste_glyph).pack(side="left", padx=(6, 0))
        ttk.Checkbutton(
            act, text="Hiện tiếng Việt theo fixed index", variable=self.show_vi_var,
            command=self.refresh_tree,
        ).pack(side="left", padx=12)
        ttk.Label(act, text="Tìm:").pack(side="left", padx=(12, 4))
        ent = ttk.Entry(act, textvariable=self.search_var, width=24)
        ent.pack(side="left")
        ent.bind("<KeyRelease>", lambda e: self.refresh_tree())

        main = ttk.Panedwindow(self, orient="horizontal")
        main.pack(fill="both", expand=True)
        left = ttk.Frame(main)
        right = ttk.Frame(main)
        main.add(left, weight=3)
        main.add(right, weight=2)

        cols = ("order", "idx", "display", "code", "page", "xy", "width", "height", "adv")
        self.tree = ttk.Treeview(left, columns=cols, show="headings", selectmode="browse")
        headings = {
            "order": "Thứ tự", "idx": "FNT #", "display": "Ký tự", "code": "Code",
            "page": "Page", "xy": "X,Y", "width": "Width", "height": "Height", "adv": "Advance",
        }
        widths = {"order": 65, "idx": 58, "display": 78, "code": 82, "page": 48, "xy": 82,
                  "width": 58, "height": 58, "adv": 65}
        for c in cols:
            self.tree.heading(c, text=headings[c])
            self.tree.column(c, width=widths[c], anchor="center")
        ys = ttk.Scrollbar(left, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=ys.set)
        self.tree.pack(side="left", fill="both", expand=True)
        ys.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_select)
        self.tree.bind("<Control-c>", lambda e: self.copy_glyph())
        self.tree.bind("<Control-v>", lambda e: self.paste_glyph())

        # Compact editor: remove the old multi-line info block. All record data is
        # already visible/editable in the fields below and in the table columns.
        metrics = ttk.LabelFrame(right, text="Edit FNT record", padding=10)
        metrics.pack(fill="x")

        fields = [
            ("Code", self.code_edit, "entry"),
            ("Page", self.page_edit, "spin_page"),
            ("X", self.x_edit, "spin_xy"),
            ("Y", self.y_edit, "spin_xy"),
            ("Width", self.width_edit, "spin_size"),
            ("Height", self.height_edit, "spin_size"),
            ("Advance", self.advance_edit, "spin_u16"),
            ("Center X", self.centerx_edit, "spin_s16"),
            ("Neg Half W", self.neghalf_edit, "spin_s16"),
            ("Neg Top", self.negtop_edit, "spin_s16"),
        ]
        for i, (label, var, kind) in enumerate(fields):
            row = i // 2
            col = (i % 2) * 2
            ttk.Label(metrics, text=label + ":").grid(row=row, column=col, sticky="e", padx=(4, 3), pady=2)
            if kind == "entry":
                w = ttk.Entry(metrics, textvariable=var, width=10)
            elif kind == "spin_page":
                w = ttk.Spinbox(metrics, from_=0, to=PAGE_COUNT-1, textvariable=var, width=8)
            elif kind == "spin_xy":
                w = ttk.Spinbox(metrics, from_=0, to=511, textvariable=var, width=8)
            elif kind == "spin_size":
                w = ttk.Spinbox(metrics, from_=1, to=512, textvariable=var, width=8)
            elif kind == "spin_u16":
                w = ttk.Spinbox(metrics, from_=0, to=65535, textvariable=var, width=8)
            else:
                w = ttk.Spinbox(metrics, from_=-32768, to=32767, textvariable=var, width=8)
            w.grid(row=row, column=col+1, sticky="w", padx=(0, 8), pady=2)

        edit_buttons = ttk.Frame(metrics)
        edit_buttons.grid(row=5, column=0, columnspan=4, sticky="w", pady=(7, 0))
        ttk.Button(edit_buttons, text="Apply ALL fields", command=self.apply_metrics).pack(side="left")
        ttk.Label(
            metrics,
            text="Advance = khoảng chạy ngang; vị trí lên/xuống do Neg Top + Height/bitmap.",
        ).grid(row=6, column=0, columnspan=4, sticky="w", pady=(6, 0))

        prev = ttk.LabelFrame(right, text="Preview", padding=10)
        prev.pack(fill="both", expand=True, pady=(10, 0))
        self.preview = ttk.Label(prev, anchor="center")
        self.preview.pack(fill="both", expand=True)
        buttons = ttk.Frame(prev)
        buttons.pack(fill="x", pady=(10, 0))
        ttk.Button(buttons, text="Export glyph này", command=self.export_selected).pack(side="left")
        ttk.Button(buttons, text="Import PNG vào glyph này", command=self.import_selected).pack(side="left", padx=6)

        ttk.Label(self, textvariable=self.status_var, anchor="w").pack(fill="x", pady=(8, 0))

    def choose_folder(self):
        p = filedialog.askdirectory(title="Chọn thư mục có Font00.fnt + Font_0000..0013.gxt.gz")
        if p:
            self.folder_var.set(p)

    def load_font(self):
        try:
            folder = Path(self.folder_var.get())
            if not folder.is_dir():
                raise ValueError("Font folder không hợp lệ.")
            self.header, self.glyphs, self.tail = load_fnt(folder / "Font00.fnt")
            validate_fixed_indices(self.glyphs)
            self.pages = {}
            for p in range(PAGE_COUNT):
                fn = folder / f"Font_{p:04d}.gxt.gz"
                if not fn.is_file():
                    raise ValueError(f"Thiếu {fn.name}.")
                self.pages[p] = list(read_gxt(fn))
            # Validate code uniqueness for Replace Tool too.
            _, rows = fixed_index_byte_map(self.glyphs)
            self.selected_index = None
            self.refresh_tree()

            iid = str(FIXED_START_INDEX)
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
                self.tree.focus(iid)
                self.tree.see(iid)
                self.on_select()
            self.status_var.set(
                f"Đã load {len(self.glyphs)} glyph. Fixed map: FNT #{FIXED_START_INDEX}..#{FIXED_END_INDEX}; "
                "không dùng vi_mapping.json."
            )
            self.aio.replace_tab.font_var.set(str(folder))
        except Exception as e:
            messagebox.showerror("Load font", str(e))

    def display_char(self, idx: int, g: Glyph):
        if self.show_vi_var.get() and idx in VI_INDEX_TO_CHAR:
            return VI_INDEX_TO_CHAR[idx]
        c = decode_fnt_code(g.code)
        if c is None:
            return "?"
        if c.isspace():
            return {" ": "[SPACE]", "\t": "[TAB]", "\r": "[CR]", "\n": "[LF]"}.get(c, repr(c))
        return c

    def refresh_tree(self):
        if not self.glyphs:
            return
        q = self.search_var.get().strip().lower()
        for item in self.tree.get_children():
            self.tree.delete(item)
        for idx, g in enumerate(self.glyphs):
            disp = self.display_char(idx, g)
            code = f"0x{g.code:04X}" if g.code <= 0xFFFF else f"0x{g.code:X}"
            map_order = idx - FIXED_START_INDEX + 1 if idx in VI_INDEX_TO_CHAR else "-"
            hay = f"{idx} {disp} {code} {g.page} {g.atlas_x},{g.atlas_y} {g.width}x{g.height}".lower()
            if q and q not in hay:
                continue
            self.tree.insert(
                "", "end", iid=str(idx),
                values=(idx + 1, idx, disp, code, g.page, f"{g.atlas_x},{g.atlas_y}", g.width, g.height, g.advance),
            )

    def on_select(self, event=None):
        sel = self.tree.selection()
        if not sel:
            return
        idx = int(sel[0])
        self.selected_index = idx
        g = self.glyphs[idx]
        self.code_edit.set(f"0x{g.code:04X}")
        self.page_edit.set(g.page)
        self.x_edit.set(g.atlas_x)
        self.y_edit.set(g.atlas_y)
        self.width_edit.set(g.width)
        self.height_edit.set(g.height)
        self.advance_edit.set(g.advance)
        self.centerx_edit.set(g.center_x)
        self.neghalf_edit.set(g.neg_half_width)
        self.negtop_edit.set(g.neg_top)
        if 0 <= g.page < PAGE_COUNT and g.width > 0 and g.height > 0:
            img = glyph_alpha_from_page(self.pages[g.page][1], g)
            scale = max(1, min(10, 220 // max(1, max(img.size))))
            prev = img.resize((img.width * scale, img.height * scale), Image.Resampling.NEAREST).convert("RGBA")
            self.preview_tk = ImageTk.PhotoImage(prev)
            self.preview.configure(image=self.preview_tk)
        else:
            self.preview.configure(image="")
            self.preview_tk = None

    def apply_metrics(self):
        """Apply every editable FNT field and safely move/resize the atlas bitmap."""
        try:
            if self.selected_index is None:
                raise ValueError("Chưa chọn glyph.")
            idx = self.selected_index
            old = self.glyphs[idx]

            code_text = self.code_edit.get().strip()
            try:
                code = int(code_text, 0)
            except Exception:
                code = int(code_text, 16)
            page = int(self.page_edit.get())
            ax = int(self.x_edit.get())
            ay = int(self.y_edit.get())
            width = int(self.width_edit.get())
            height = int(self.height_edit.get())
            advance = int(self.advance_edit.get())
            center_x = int(self.centerx_edit.get())
            neg_half = int(self.neghalf_edit.get())
            neg_top = int(self.negtop_edit.get())

            if not (1 <= code <= 0xFFFF):
                raise ValueError("Code phải nằm trong 0x0001..0xFFFF.")
            if not (0 <= page < PAGE_COUNT):
                raise ValueError(f"Page phải nằm trong 0..{PAGE_COUNT-1}.")
            if width <= 0 or height <= 0:
                raise ValueError("Width/Height phải > 0.")
            if not (0 <= ax < PAGE_W and 0 <= ay < PAGE_H):
                raise ValueError("X/Y phải nằm trong atlas 512x512.")
            if ax + width > PAGE_W or ay + height > PAGE_H:
                raise ValueError("X/Y + Width/Height vượt khỏi atlas 512x512.")
            if not (0 <= advance <= 0xFFFF):
                raise ValueError("Advance phải nằm trong 0..65535.")
            for name, value in (("Center X", center_x), ("Neg Half W", neg_half), ("Neg Top", neg_top)):
                if not (-32768 <= value <= 32767):
                    raise ValueError(f"{name} vượt phạm vi signed 16-bit.")

            # Fixed block may change code, but raw bytes must stay unique so Replace Tool remains deterministic.
            if idx in VI_INDEX_TO_CHAR:
                for other_idx in range(FIXED_START_INDEX, FIXED_END_INDEX + 1):
                    if other_idx != idx and self.glyphs[other_idx].code == code:
                        raise ValueError(
                            f"Code 0x{code:04X} đã được FNT #{other_idx} dùng trong fixed map; "
                            "Replace Tool sẽ bị trùng raw byte."
                        )

            geometry_changed = (
                page != old.page or ax != old.atlas_x or ay != old.atlas_y or
                width != old.width or height != old.height
            )

            if geometry_changed:
                if not (0 <= old.page < PAGE_COUNT and old.width > 0 and old.height > 0):
                    raise ValueError("Glyph cũ không có bitmap hợp lệ để move/resize.")
                img = glyph_alpha_from_page(self.pages[old.page][1], old)
                if img.size != (width, height):
                    img = img.resize((width, height), Image.Resampling.LANCZOS)

                occ = build_occupancy(self.glyphs, 0, exclude_indices={idx})
                if not rect_is_free(occ[page], ax, ay, width, height, 0):
                    raise ValueError(
                        "Vùng Page/X/Y/Width/Height mới đang đè lên glyph khác. "
                        "Hãy đổi tọa độ hoặc kích thước."
                    )
                clear_glyph_rect(self.pages[old.page][1], old)
                paint_glyph(self.pages[page][1], img, ax, ay)

            self.glyphs[idx] = Glyph(
                code=code,
                page=page,
                center_x=center_x,
                neg_half_width=neg_half,
                neg_top=neg_top,
                advance=advance,
                width=width,
                height=height,
                atlas_x=ax,
                atlas_y=ay,
            )

            self.refresh_tree()
            iid = str(idx)
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
                self.tree.focus(iid)
                self.tree.see(iid)
            self.on_select()
            self.status_var.set(f"Đã cập nhật toàn bộ FNT fields #{idx}. Chưa ghi file.")
        except Exception as e:
            messagebox.showerror("Apply ALL fields", str(e))

    def copy_glyph(self):
        try:
            if self.selected_index is None:
                raise ValueError("Chưa chọn glyph.")
            g = self.glyphs[self.selected_index]
            img = glyph_alpha_from_page(self.pages[g.page][1], g).copy()
            self.glyph_clipboard = {
                "image": img,
                "advance": g.advance,
                "center_x": g.center_x,
                "neg_half_width": g.neg_half_width,
                "neg_top": g.neg_top,
                "source_index": self.selected_index,
            }
            self.status_var.set(f"Đã Copy glyph FNT #{self.selected_index} ({self.display_char(self.selected_index, g)}).")
        except Exception as e:
            messagebox.showerror("Copy glyph", str(e))

    def paste_glyph(self):
        try:
            if self.selected_index is None:
                raise ValueError("Chưa chọn glyph đích.")
            if not self.glyph_clipboard:
                raise ValueError("Clipboard glyph đang trống. Hãy Copy glyph trước.")
            idx = self.selected_index
            old = self.glyphs[idx]
            clip = self.glyph_clipboard
            img = clip["image"].copy()
            w, h = img.size

            # Free the destination record when searching. This allows reusing its
            # old atlas rectangle if the copied glyph fits there.
            occ = build_occupancy(self.glyphs, 1, exclude_indices={idx})
            pos = find_space(occ, w, h, 1)
            if pos is None:
                raise RuntimeError(f"Không còn chỗ atlas cho glyph copy {w}x{h}.")
            page, ax, ay = pos

            clear_glyph_rect(self.pages[old.page][1], old)
            paint_glyph(self.pages[page][1], img, ax, ay)
            self.glyphs[idx] = Glyph(
                code=old.code,                    # fixed-index/raw-byte contract preserved
                page=page,
                center_x=int(clip["center_x"]),
                neg_half_width=int(clip["neg_half_width"]),
                neg_top=int(clip["neg_top"]),
                advance=int(clip["advance"]),
                width=w,
                height=h,
                atlas_x=ax,
                atlas_y=ay,
            )
            self.refresh_tree()
            iid = str(idx)
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
                self.tree.focus(iid)
                self.tree.see(iid)
            self.on_select()
            self.status_var.set(
                f"Đã Paste glyph từ FNT #{clip['source_index']} -> #{idx}. Code đích giữ nguyên. Chưa ghi file."
            )
        except Exception as e:
            messagebox.showerror("Paste glyph", str(e))

    def export_selected(self):
        try:
            if self.selected_index is None:
                raise ValueError("Chưa chọn glyph.")
            g = self.glyphs[self.selected_index]
            folder = filedialog.askdirectory(title="Chọn thư mục xuất glyph")
            if not folder:
                return
            out = Path(folder)
            img = glyph_alpha_from_page(self.pages[g.page][1], g)
            vi = VI_INDEX_TO_CHAR.get(self.selected_index)
            suffix = f"_{vi}" if vi else ""
            safe = f"{self.selected_index:04d}_0x{g.code:04X}{suffix}"
            img.save(out / f"{safe}.png")
            meta = {
                "index": self.selected_index,
                "display": self.display_char(self.selected_index, g),
                "fixed_vi": vi,
                "code": f"0x{g.code:04X}",
                "page": g.page,
                "x": g.atlas_x,
                "y": g.atlas_y,
                "width": g.width,
                "height": g.height,
                "advance": g.advance,
                "center_x": g.center_x,
                "neg_half_width": g.neg_half_width,
                "neg_top": g.neg_top,
            }
            (out / f"{safe}.json").write_text(json.dumps(meta, ensure_ascii=False, indent=2), encoding="utf-8")
            self.status_var.set(f"Đã export glyph {safe}.")
        except Exception as e:
            messagebox.showerror("Export glyph", str(e))

    def import_selected(self):
        try:
            if self.selected_index is None:
                raise ValueError("Chưa chọn glyph.")
            p = filedialog.askopenfilename(
                title="Import glyph PNG",
                filetypes=[("PNG", "*.png"), ("Image", "*.png *.bmp *.gif *.tif *.tiff"), ("All files", "*.*")],
            )
            if not p:
                return

            idx = self.selected_index
            old = self.glyphs[idx]
            img = image_to_glyph_alpha(Image.open(p))
            w, h = img.size
            if w <= 0 or h <= 0 or w > PAGE_W or h > PAGE_H:
                raise ValueError(f"Kích thước ảnh {w}x{h} không hợp lệ cho atlas 512x512.")

            # Prefer the current atlas position if the imported bitmap still fits there.
            occ = build_occupancy(self.glyphs, 1, exclude_indices={idx})
            pos = None
            if (
                0 <= old.page < PAGE_COUNT and
                old.atlas_x + w <= PAGE_W and old.atlas_y + h <= PAGE_H and
                rect_is_free(occ[old.page], old.atlas_x, old.atlas_y, w, h, 1)
            ):
                pos = (old.page, old.atlas_x, old.atlas_y)
            if pos is None:
                pos = find_space(occ, w, h, 1)
            if pos is None:
                raise RuntimeError(f"Không còn chỗ atlas cho PNG {w}x{h}.")
            page, ax, ay = pos

            clear_glyph_rect(self.pages[old.page][1], old)
            paint_glyph(self.pages[page][1], img, ax, ay)

            self.glyphs[idx] = Glyph(
                code=old.code,
                page=page,
                center_x=old.center_x,
                neg_half_width=-(w // 2),
                neg_top=old.neg_top,
                advance=old.advance,
                width=w,
                height=h,
                atlas_x=ax,
                atlas_y=ay,
            )

            self.refresh_tree()
            iid = str(idx)
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
                self.tree.focus(iid)
                self.tree.see(iid)
            self.on_select()
            self.status_var.set(
                f"Đã Import glyph PNG {w}x{h} vào FNT #{idx}; Width/Height cập nhật theo ảnh. Chưa ghi file."
            )
        except Exception as e:
            messagebox.showerror("Import glyph", str(e))

    def write_current_to(self, outp: Path):
        if not self.glyphs:
            raise ValueError("Chưa load font.")
        src = Path(self.folder_var.get())
        outp.mkdir(parents=True, exist_ok=True)
        if src.resolve() != outp.resolve():
            for item in src.iterdir():
                if item.is_file():
                    shutil.copy2(item, outp / item.name)
        for p in range(PAGE_COUNT):
            write_gxt(outp / f"Font_{p:04d}.gxt.gz", self.pages[p][0], self.pages[p][1], self.pages[p][2])
        save_fnt(outp / "Font00.fnt", self.header, self.glyphs, self.tail)

    def save_current(self):
        try:
            if not self.glyphs:
                raise ValueError("Chưa load font.")
            out = filedialog.askdirectory(title="Chọn thư mục ghi font hiện tại")
            if not out:
                return
            outp = Path(out)
            self.write_current_to(outp)
            self.status_var.set(f"Đã ghi font: {outp}")
            self.aio.replace_tab.font_var.set(str(outp))
            messagebox.showinfo("Save font", f"Đã ghi font vào:\n{outp}")
        except Exception as e:
            messagebox.showerror("Save font", str(e))

    def export_font(self):
        try:
            if not self.glyphs:
                raise ValueError("Chưa load font.")
            folder = filedialog.askdirectory(title="Chọn thư mục Export Font")
            if not folder:
                return
            out = Path(folder)
            glyph_dir = out / "glyphs"
            glyph_dir.mkdir(parents=True, exist_ok=True)
            manifest = []
            for idx, g in enumerate(self.glyphs):
                disp = self.display_char(idx, g)
                fn = None
                if 0 <= g.page < PAGE_COUNT and g.width > 0 and g.height > 0:
                    vi = VI_INDEX_TO_CHAR.get(idx)
                    suffix = f"_{vi}" if vi else ""
                    fn = f"{idx:04d}_0x{g.code:04X}{suffix}.png"
                    glyph_alpha_from_page(self.pages[g.page][1], g).save(glyph_dir / fn)
                manifest.append({
                    "index": idx,
                    "display": disp,
                    "fixed_vi": VI_INDEX_TO_CHAR.get(idx),
                    "code": f"0x{g.code:04X}",
                    "page": g.page,
                    "x": g.atlas_x,
                    "y": g.atlas_y,
                    "width": g.width,
                    "height": g.height,
                    "advance": g.advance,
                    "center_x": g.center_x,
                    "neg_half_width": g.neg_half_width,
                    "neg_top": g.neg_top,
                    "png": fn,
                })
            (out / "font_manifest.json").write_text(
                json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8"
            )
            messagebox.showinfo("Export Font", f"Đã xuất {len(manifest)} glyph vào:\n{out}")
        except Exception as e:
            messagebox.showerror("Export Font", str(e))

    def import_font(self):
        try:
            if not self.glyphs:
                raise ValueError("Chưa load font.")
            folder = filedialog.askdirectory(title="Chọn thư mục Export Font đã chỉnh")
            if not folder:
                return
            base = Path(folder)
            manifest_path = base / "font_manifest.json"
            glyph_dir = base / "glyphs"
            if not manifest_path.is_file():
                raise ValueError("Thiếu font_manifest.json.")
            data = json.loads(manifest_path.read_text(encoding="utf-8"))
            changed = 0
            for ent in data:
                idx = ent.get("index")
                fn = ent.get("png")
                if not isinstance(idx, int) or not (0 <= idx < len(self.glyphs)) or not fn:
                    continue
                p = glyph_dir / fn
                if not p.is_file():
                    continue
                g = self.glyphs[idx]
                paint_alpha(self.pages[g.page][1], g, Image.open(p).convert("L"))
                changed += 1

            out = filedialog.askdirectory(title="Chọn thư mục ghi font đã import")
            if not out:
                return
            outp = Path(out)
            self.write_current_to(outp)
            self.aio.replace_tab.font_var.set(str(outp))
            messagebox.showinfo("Import Font", f"Đã import {changed} glyph và ghi font vào:\n{outp}")
        except Exception as e:
            messagebox.showerror("Import Font", str(e))


# -----------------------------------------------------------------------------
# Tab 3 - Replace Tool (exact bytes from same fixed indices)
# -----------------------------------------------------------------------------

class ReplaceToolTab(ttk.Frame):
    def __init__(self, parent, aio):
        super().__init__(parent, padding=16)
        self.aio = aio
        self.font_var = tk.StringVar()
        self.folder_var = tk.StringVar()
        self.status_var = tk.StringVar(value="Chọn font folder và thư mục text.")
        self.build_ui()

    def build_ui(self):
        title = ttk.Label(self, text="DFCI Replace Tool - Fixed Index", font=("Segoe UI", 14, "bold"))
        title.pack(anchor="w", pady=(0, 10))

        box = ttk.LabelFrame(self, text="Input", padding=10)
        box.pack(fill="x")
        add_path_row(box, 0, "Font folder:", self.font_var, self.pick_font_folder)

        ttk.Label(box, text="Text / CSV:", width=18).grid(row=1, column=0, sticky="w", pady=4)
        ttk.Entry(box, textvariable=self.folder_var).grid(row=1, column=1, sticky="ew", padx=6)
        pick = ttk.Frame(box)
        pick.grid(row=1, column=2, sticky="e")
        ttk.Button(pick, text="Thư mục…", command=self.pick_text_folder).pack(side="left")
        ttk.Button(pick, text="File…", command=self.pick_text_file).pack(side="left", padx=(4, 0))
        box.grid_columnconfigure(1, weight=1)

        ttk.Label(
            self,
            text=(
                f"Built-in map: {FIXED_COUNT} ký tự. Replace Tool KHÔNG dùng vi_mapping.json và KHÔNG giả định F040. "
                f"Nó đọc code thật tại FNT #{FIXED_START_INDEX}..#{FIXED_END_INDEX}, rồi ghi đúng raw byte của từng code. "
                "Nhận TXT/CSV/TSV và các file text phổ biến; có thể chọn cả thư mục hoặc một file. "
                "File có thay đổi được xuất CP932."
            ),
            wraplength=1000,
        ).pack(anchor="w", pady=(10, 0))

        actions = ttk.Frame(self)
        actions.pack(fill="x", pady=(12, 8))
        ttk.Button(actions, text="Kiểm tra map theo Font00.fnt", command=self.analyze_map).pack(side="left")
        ttk.Button(actions, text="TẠO BẢN _vi", command=self.run).pack(side="left", padx=8)
        ttk.Button(actions, text="Dùng output Font Tool", command=self.use_builder_output).pack(side="left")

        ttk.Label(self, textvariable=self.status_var, wraplength=1000).pack(anchor="w")
        logframe = ttk.LabelFrame(self, text="Log", padding=8)
        logframe.pack(fill="both", expand=True, pady=(10, 0))
        self.log = LogBox(logframe, height=18)
        ys = ttk.Scrollbar(logframe, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=ys.set)
        self.log.pack(side="left", fill="both", expand=True)
        ys.pack(side="right", fill="y")

    def pick_font_folder(self):
        p = filedialog.askdirectory(title="Chọn font folder chứa Font00.fnt")
        if p:
            self.font_var.set(p)

    def pick_text_folder(self):
        p = filedialog.askdirectory(title="Chọn thư mục text / CSV")
        if p:
            self.folder_var.set(p)

    def pick_text_file(self):
        p = filedialog.askopenfilename(
            title="Chọn file text / CSV",
            filetypes=[
                ("CSV / TSV", "*.csv *.tsv"),
                ("Text", "*.txt *.csv *.tsv *.ini *.cfg *.json *.xml *.yml *.yaml *.lua *.ks *.scr *.script *.msg *.mes *.dat *.lst *.tbl *.po *.srt *.ass *.sub"),
                ("All files", "*.*"),
            ],
        )
        if p:
            self.folder_var.set(p)

    def use_builder_output(self):
        p = self.aio.font_tab.out_var.get().strip()
        if p:
            self.font_var.set(p)

    def load_fixed_map(self):
        font_folder = Path(self.font_var.get())
        if not font_folder.is_dir():
            raise ValueError("Chưa chọn font folder hợp lệ.")
        fnt = font_folder / "Font00.fnt"
        if not fnt.is_file():
            raise ValueError("Thiếu Font00.fnt trong font folder.")
        _, glyphs, _ = load_fnt(fnt)
        char_to_bytes, rows = fixed_index_byte_map(glyphs)
        return glyphs, char_to_bytes, rows

    def analyze_map(self):
        try:
            self.log.clear()
            glyphs, mp, rows = self.load_fixed_map()
            self.log.write_line(f"Font glyphs: {len(glyphs)}")
            self.log.write_line(f"Fixed block: #{FIXED_START_INDEX}..#{FIXED_END_INDEX}")
            self.log.write_line(f"Map entries: {len(mp)}")
            self.log.write_line("")
            for order, idx, char, code, raw, placeholder in rows[:20]:
                self.log.write_line(
                    f"{order:03d}. FNT #{idx:04d} {char} -> 0x{code:04X} -> "
                    f"{raw.hex(' ').upper()}  ({placeholder!r})"
                )
            self.log.write_line("...")
            order, idx, char, code, raw, placeholder = rows[-1]
            self.log.write_line(
                f"{order:03d}. FNT #{idx:04d} {char} -> 0x{code:04X} -> "
                f"{raw.hex(' ').upper()}  ({placeholder!r})"
            )
            self.status_var.set("Fixed-index map hợp lệ; code không trùng.")
        except Exception as e:
            self.status_var.set("Map lỗi.")
            self.log.write_line(traceback.format_exc())
            messagebox.showerror("Kiểm tra map", str(e))

    def run(self):
        try:
            src = Path(self.folder_var.get()).resolve()
            if not src.exists() or not (src.is_dir() or src.is_file()):
                raise ValueError("Chưa chọn file hoặc thư mục text/CSV hợp lệ.")
            glyphs, char_to_bytes, rows = self.load_fixed_map()

            single_file = src.is_file()
            if single_file:
                dst = src.with_name(src.stem + "_vi" + src.suffix)
                if dst.exists() and not messagebox.askyesno(
                    "File đã tồn tại",
                    f"{dst.name} đã tồn tại.\n\nGhi đè?",
                ):
                    return
            else:
                dst = src.parent / (src.name + "_vi")
                if dst.exists():
                    if not messagebox.askyesno(
                        "Thư mục đã tồn tại",
                        f"{dst.name} đã tồn tại.\n\nXóa và tạo lại?",
                    ):
                        return
                    shutil.rmtree(dst)

            self.log.clear()
            self.log.write_line(f"Font   : {Path(self.font_var.get()).resolve()}")
            self.log.write_line(f"Text   : {src}")
            self.log.write_line(f"Output : {dst}")
            self.log.write_line(
                f"Map    : fixed FNT index #{FIXED_START_INDEX}..#{FIXED_END_INDEX}; "
                "không dùng vi_mapping.json"
            )
            self.log.write_line("")

            if not single_file:
                dst.mkdir(parents=True)

            files_total = 0
            files_changed = 0
            replacements = 0
            binaries = 0

            def process_one(inp: Path, out: Path, label: str):
                nonlocal files_total, files_changed, replacements, binaries
                files_total += 1
                raw = inp.read_bytes()
                dec = decode_text(raw, inp.suffix)
                if dec is None:
                    if single_file:
                        raise ValueError(
                            f"Không nhận diện được {inp.name} là text/CSV hỗ trợ. "
                            "Hỗ trợ CSV UTF-8, UTF-8 BOM, UTF-16 LE/BE, CP932 và CP1258."
                        )
                    shutil.copy2(inp, out)
                    binaries += 1
                    self.log.write_line(f"COPY      {label}")
                    return

                text, enc = dec
                n_expected = sum(text.count(c) for c in VI_MAPPING_ORDER)
                if n_expected == 0:
                    if single_file:
                        out.write_bytes(raw)
                        try:
                            shutil.copystat(inp, out)
                        except Exception:
                            pass
                    else:
                        shutil.copy2(inp, out)
                    self.log.write_line(f"UNCHANGED {label}  [{enc}]")
                    return

                try:
                    outbytes, n = encode_fixed_index_cp932(text, char_to_bytes)
                except FixedTextEncodeError as e:
                    raise RuntimeError(
                        f"{label} còn ký tự không encode được CP932: {e.char!r} "
                        f"(vị trí {e.position}).\n"
                        "Ký tự Việt trong fixed map được xử lý trực tiếp bằng raw byte; lỗi này là ký tự khác ngoài CP932."
                    ) from e

                out.parent.mkdir(parents=True, exist_ok=True)
                out.write_bytes(outbytes)
                try:
                    shutil.copystat(inp, out)
                except Exception:
                    pass
                files_changed += 1
                replacements += n
                self.log.write_line(f"REPLACE   {label}  [{enc} -> CP932 fixed-index]  {n}")

            if single_file:
                process_one(src, dst, src.name)
            else:
                for cur, dirs, files in os.walk(src):
                    curp = Path(cur)
                    rel = curp.relative_to(src)
                    outdir = dst / rel
                    outdir.mkdir(parents=True, exist_ok=True)
                    for name in files:
                        inp = curp / name
                        out = outdir / name
                        process_one(inp, out, str(inp.relative_to(src)))

            self.status_var.set(
                f"Hoàn tất — {replacements} ký tự / {files_changed} file. Output: {dst.name}"
            )
            self.log.write_line("")
            self.log.write_line(f"Hoàn tất: {replacements} ký tự trong {files_changed}/{files_total} file.")
            self.log.write_line(f"Binary/không xác định: {binaries}" + ("." if single_file else " (copy nguyên)."))
            self.log.write_line(f"Output: {dst}")
            messagebox.showinfo(
                "Hoàn tất",
                f"Đã tạo:\n{dst}\n\n"
                f"File: {files_total}\nFile thay đổi: {files_changed}\nKý tự đã thay: {replacements}",
            )
        except Exception as e:
            self.status_var.set("Có lỗi.")
            self.log.write_line("")
            self.log.write_line("ERROR:")
            self.log.write_line(traceback.format_exc())
            messagebox.showerror("Replace Tool", str(e))


# -----------------------------------------------------------------------------
# AIO shell
# -----------------------------------------------------------------------------

class DFCIAIO(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1280x820")
        self.minsize(1080, 700)

        style = ttk.Style(self)
        try:
            style.configure("TNotebook.Tab", padding=(14, 7))
        except Exception:
            pass

        notebook = ttk.Notebook(self)
        notebook.pack(fill="both", expand=True)

        self.font_tab = FontToolTab(notebook, self)
        self.editor_tab = FontEditorTab(notebook, self)
        self.replace_tab = ReplaceToolTab(notebook, self)

        notebook.add(self.font_tab, text="1. Font Tool")
        notebook.add(self.editor_tab, text="2. Font Editor")
        notebook.add(self.replace_tab, text="3. Replace Tool")

        footer = ttk.Label(
            self,
            text=(
                f"Fixed-index master map: FNT #{FIXED_START_INDEX}=á … #{FIXED_END_INDEX}=Ỵ | "
                "Không dùng vi_mapping.json | Replace lấy raw byte trực tiếp từ Font00.fnt"
            ),
            anchor="w",
        )
        footer.pack(fill="x", padx=10, pady=(0, 6))


if __name__ == "__main__":
    if len(VI_MAPPING_ORDER) != 134 or len(set(VI_MAPPING_ORDER)) != 134:
        raise SystemExit("Internal error: Vietnamese fixed map must contain exactly 134 unique characters.")
    DFCIAIO().mainloop()
