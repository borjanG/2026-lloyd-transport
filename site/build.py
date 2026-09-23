#!/usr/bin/env python3
"""Build site/data.js from the paper's LaTeX source.

Usage (from the repository root):

    python3 site/build.py                 # uses site/source/v7.tex and v7.bbl
    python3 site/build.py --tex path/to/v7.tex --bbl path/to/v7.bbl --aux path/to/v7.aux

The script converts a small, well-defined subset of LaTeX (the one used by
the manuscript) into HTML.  Mathematics is left as TeX inside
``data-tex`` attributes and rendered in the browser with KaTeX.  Everything
that is not the paper's own text (summaries, proof ideas, the dependency
graph, Lean coverage) lives in ``site/content/nodes.json`` and
``site/content/meta.json``.  Run ``node site/tools/check-math.mjs`` afterwards
to make sure every formula renders.
"""
from __future__ import annotations

import argparse
import html
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent

THEOREM_ENVS = ("theorem", "proposition", "lemma", "corollary", "definition", "remark", "example")
KIND_LABEL = {
    "theorem": "Theorem", "proposition": "Proposition", "lemma": "Lemma", "corollary": "Corollary",
    "definition": "Definition", "remark": "Remark", "example": "Example",
}
REF_WORDS = ("Theorem", "Corollary", "Proposition", "Lemma", "Remark", "Figure", "Section", "Appendix",
             "Definition", "Example", "Equation")

# --------------------------------------------------------------------------- utilities


def strip_comments(tex: str) -> str:
    out = []
    for line in tex.split("\n"):
        i, res = 0, ""
        while True:
            j = line.find("%", i)
            if j < 0:
                res += line[i:]
                break
            k, n = j - 1, 0
            while k >= 0 and line[k] == "\\":
                n += 1
                k -= 1
            if n % 2 == 1:  # escaped percent sign
                res += line[i:j + 1]
                i = j + 1
                continue
            res += line[i:j]
            break
        out.append(res)
    return "\n".join(out)


def read_group(s: str, i: int) -> tuple[str, int]:
    """s[i] == '{'. Return (content, index after the closing brace)."""
    assert s[i] == "{", (i, s[i:i + 20])
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    raise ValueError("unbalanced braces at %d" % i)


def read_opt(s: str, i: int) -> tuple[str | None, int]:
    """Optional [..] argument starting at i (after whitespace)."""
    j = i
    while j < len(s) and s[j] in " \t":
        j += 1
    if j < len(s) and s[j] == "[":
        depth, k = 0, j
        while k < len(s):
            if s[k] == "[":
                depth += 1
            elif s[k] == "]":
                depth -= 1
                if depth == 0:
                    return s[j + 1:k], k + 1
            k += 1
    return None, i


def find_env_end(s: str, name: str, start: int) -> tuple[int, int]:
    """start points just after \\begin{name}. Return (body_end, after_end)."""
    pat = re.compile(r"\\(begin|end)\{" + re.escape(name) + r"\}")
    depth = 1
    for m in pat.finditer(s, start):
        if m.group(1) == "begin":
            depth += 1
        else:
            depth -= 1
            if depth == 0:
                return m.start(), m.end()
    raise ValueError("unterminated environment " + name)


def split_top_level(s: str, sep: str = r"\\\\") -> list[str]:
    """Split s on `\\\\` occurring outside braces and nested environments."""
    parts, depth, i, cur = [], 0, 0, ""
    env_depth = 0
    while i < len(s):
        if s.startswith("\\begin{", i):
            env_depth += 1
        elif s.startswith("\\end{", i):
            env_depth -= 1
        if s[i] == "\\" and i + 1 < len(s):
            if s[i + 1] == "\\" and depth == 0 and env_depth == 0:
                parts.append(cur)
                cur = ""
                i += 2
                continue
            cur += s[i:i + 2]
            i += 2
            continue
        if s[i] == "{":
            depth += 1
        elif s[i] == "}":
            depth -= 1
        cur += s[i]
        i += 1
    parts.append(cur)
    return parts


ACCENTS = {
    '"': {"a": "ä", "e": "ë", "i": "ï", "o": "ö", "u": "ü", "A": "Ä", "E": "Ë", "I": "Ï", "O": "Ö", "U": "Ü", "y": "ÿ"},
    "'": {"a": "á", "e": "é", "i": "í", "o": "ó", "u": "ú", "A": "Á", "E": "É", "I": "Í", "O": "Ó", "U": "Ú", "y": "ý", "c": "ć", "n": "ń"},
    "`": {"a": "à", "e": "è", "i": "ì", "o": "ò", "u": "ù", "A": "À", "E": "È", "I": "Ì", "O": "Ò", "U": "Ù"},
    "^": {"a": "â", "e": "ê", "i": "î", "o": "ô", "u": "û", "A": "Â", "E": "Ê", "I": "Î", "O": "Ô", "U": "Û"},
    "~": {"a": "ã", "n": "ñ", "o": "õ", "A": "Ã", "N": "Ñ", "O": "Õ"},
    "c": {"c": "ç", "C": "Ç"},
    "v": {"c": "č", "s": "š", "z": "ž", "C": "Č", "S": "Š", "Z": "Ž", "r": "ř", "e": "ě"},
}


def apply_accents(s: str) -> str:
    def rep(m):
        acc, ch = m.group(1), m.group(2)
        return ACCENTS.get(acc, {}).get(ch, ch)
    # \"i  \"{i}  {\"i}  \'e  \c{c}  \v{c}
    s = re.sub(r"\{\\([\"'`^~cv])\{?([A-Za-z])\}?\}", rep, s)
    s = re.sub(r"\\([\"'`^~])\{?([A-Za-z])\}?", rep, s)
    s = re.sub(r"\\([cv])\{([A-Za-z])\}", rep, s)
    s = re.sub(r"\\([cv]) ([A-Za-z])", rep, s)
    s = s.replace("\\o{}", "ø").replace("\\o ", "ø").replace("\\ss{}", "ß").replace("\\ae{}", "æ")
    s = re.sub(r"\\o(?=[^A-Za-z])", "ø", s)
    return s


# --------------------------------------------------------------------------- the converter


class Converter:
    """Turns manuscript LaTeX into HTML.  One instance per build."""

    def __init__(self, numbers: dict, labels: dict, bibkeys: dict, node_of_label: dict):
        self.numbers = numbers            # label -> printed number, for equations, theorems, sections, figures
        self.labels = labels              # label -> {"type":..., "num":...}
        self.bibkeys = bibkeys            # bib key -> {"num": n, "text": plain}
        self.node_of_label = node_of_label  # label -> node id that displays it (filled by build)
        self.eq_seen: dict[str, list[str]] = {}  # label -> [node ids whose HTML contains it]
        self.current_node: str | None = None
        self.warnings: list[str] = []
        self.unknown_cmds: dict[str, int] = {}

    # ---- math ---------------------------------------------------------------

    def math_inline(self, tex: str) -> str:
        tex = tex.strip()
        return '<span class="math" data-tex="%s"></span>' % html.escape(tex, quote=True)

    def math_display(self, env: str, body: str, opening: str | None = None) -> str:
        labels = re.findall(r"\\label\{([^}]*)\}", body)
        tex = body
        if env in ("equation", "align"):
            if env == "equation":
                tex = re.sub(r"\\label\{[^}]*\}", "", tex)
                if "\\tag" not in tex:
                    if labels:
                        tex = tex.rstrip() + " \\tag{%s}" % self.numbers[labels[0]]
                    else:
                        self.warnings.append("numbered equation without label: " + body[:60])
            else:
                rows = split_top_level(body)
                out_rows = []
                for row in rows:
                    rl = re.findall(r"\\label\{([^}]*)\}", row)
                    r = re.sub(r"\\label\{[^}]*\}", "", row)
                    notag = bool(re.search(r"\\notag|\\nonumber", r))
                    r = re.sub(r"\\notag|\\nonumber", "", r)
                    if rl:
                        r = r.rstrip() + " \\tag{%s}" % self.numbers[rl[0]]
                    elif not notag and r.strip():
                        self.warnings.append("numbered align row without label: " + row[:60])
                    out_rows.append(r)
                tex = "\\begin{align}" + "\\\\".join(out_rows) + "\\end{align}"
        elif env in ("equation*", "align*", "gather*"):
            tex = re.sub(r"\\label\{[^}]*\}", "", body)
            if env != "equation*":
                tex = "\\begin{%s}%s\\end{%s}" % (env, tex, env)
        else:  # \[ \] or $$ $$
            tex = re.sub(r"\\label\{[^}]*\}", "", body)
        tex = tex.strip()
        attrs = ' class="math-display" data-tex="%s"' % html.escape(tex, quote=True)
        if labels:
            attrs += ' id="%s" data-labels="%s"' % (html.escape(labels[0]), html.escape(" ".join(labels)))
            for lab in labels:
                if self.current_node:
                    self.eq_seen.setdefault(lab, [])
                    if self.current_node not in self.eq_seen[lab]:
                        self.eq_seen[lab].append(self.current_node)
        return "<div%s></div>" % attrs

    # ---- prose --------------------------------------------------------------

    DISPLAY_ENVS = ("equation*", "equation", "align*", "align", "gather*")

    def prose(self, tex: str, stash: list | None = None) -> str:
        """Convert a run of body text (paragraphs, lists, display maths) to HTML."""
        outermost = stash is None
        if outermost:
            stash = []

        def keep(h: str) -> str:
            stash.append(h)
            return "\x00%d\x00" % (len(stash) - 1)

        s = tex
        # 1. display maths environments -> placeholders
        s = self._extract_display(s, keep)
        # 2. lists -> placeholders (recursively converted, sharing the stash)
        s = self._extract_lists(s, keep, stash)
        # 3. paragraphs
        paras = re.split(r"\n\s*\n", s.strip())
        out = []
        for p in paras:
            p = p.strip()
            if not p:
                continue
            # a paragraph made only of placeholders (display maths / lists) is emitted bare
            if re.fullmatch(r"(\x00\d+\x00\s*)+", p):
                out.append(p)
                continue
            inner = self.inline(p)
            # split around block placeholders so <div>s are not nested in <p>
            pieces = re.split(r"(\x00\d+\x00)", inner)
            buf = ""
            for piece in pieces:
                if re.fullmatch(r"\x00\d+\x00", piece):
                    idx = int(piece.strip("\x00"))
                    if stash[idx].startswith("<div class=\"math-display\"") or stash[idx].startswith("<ol") or stash[idx].startswith("<ul"):
                        if buf.strip():
                            out.append("<p>%s</p>" % buf.strip())
                        buf = ""
                        out.append(piece)
                    else:
                        buf += piece
                else:
                    buf += piece
            if buf.strip():
                out.append("<p>%s</p>" % buf.strip())
        res = "\n".join(out)
        if not outermost:
            return res
        # restore placeholders (may be nested: lists contain display maths)
        for _ in range(8):
            if "\x00" not in res:
                break
            res = re.sub(r"\x00(\d+)\x00", lambda m: stash[int(m.group(1))], res)
        return res

    def _extract_display(self, s: str, keep) -> str:
        out, i = "", 0
        pat = re.compile(r"\\begin\{(equation\*?|align\*?|gather\*?)\}|\\\[|\$\$")
        while True:
            m = pat.search(s, i)
            if not m:
                out += s[i:]
                break
            out += s[i:m.start()]
            if m.group(0) == "\\[":
                j = s.index("\\]", m.end())
                out += keep(self.math_display("[]", s[m.end():j]))
                i = j + 2
            elif m.group(0) == "$$":
                j = s.index("$$", m.end())
                out += keep(self.math_display("$$", s[m.end():j]))
                i = j + 2
            else:
                env = m.group(1)
                body_end, after = find_env_end(s, env, m.end())
                out += keep(self.math_display(env, s[m.end():body_end]))
                i = after
        return out

    def _extract_lists(self, s: str, keep, stash: list) -> str:
        out, i = "", 0
        pat = re.compile(r"\\begin\{(itemize|enumerate)\}")
        while True:
            m = pat.search(s, i)
            if not m:
                out += s[i:]
                break
            out += s[i:m.start()]
            env = m.group(1)
            body_end, after = find_env_end(s, env, m.end())
            body = s[m.end():body_end]
            opt, k = read_opt(body, 0)
            body = body[k:]
            cls = ""
            if opt and "roman" in opt:
                cls = ' class="roman"'
            elif opt and "alph" in opt:
                cls = ' class="alpha"'
            items = re.split(r"\\item\b", body)
            lis = []
            for it in items[1:]:
                it = re.sub(r"\\smallskip|\\medskip|\\bigskip", "", it)
                lis.append("<li>%s</li>" % self.prose(it, stash))
            tag = "ul" if env == "itemize" else "ol"
            out += keep("<%s%s>%s</%s>" % (tag, cls, "".join(lis), tag))
            i = after
        return out

    # ---- inline text --------------------------------------------------------

    def inline(self, tex: str) -> str:
        """Convert inline text (no display maths / lists) to HTML."""
        stash: list[str] = []
        s = self._inline(tex, stash)
        for _ in range(8):
            if "\x01" not in s:
                break
            s = re.sub(r"\x01(\d+)\x01", lambda m: stash[int(m.group(1))], s)
        return s

    def _inline(self, tex: str, stash: list) -> str:
        """Inline conversion sharing `stash` with nested calls (placeholders stay unresolved)."""
        def keep(h: str) -> str:
            stash.append(h)
            return "\x01%d\x01" % (len(stash) - 1)

        s = tex
        s = self._extract_inline_math(s, keep)
        s = self._commands(s, keep, stash)
        s = self._typography(s)
        s = html.escape(s, quote=False)
        s = re.sub(r"[ \t]+", " ", s)
        s = re.sub(r" ?\n ?", " ", s)
        return s.strip()

    def _extract_inline_math(self, s: str, keep) -> str:
        out, i = "", 0
        while i < len(s):
            c = s[i]
            if c == "\\" and i + 1 < len(s):
                if s[i + 1] == "(":
                    j = s.index("\\)", i + 2)
                    out += keep(self.math_inline(s[i + 2:j]))
                    i = j + 2
                    continue
                out += s[i:i + 2]
                i += 2
                continue
            if c == "$":
                j = i + 1
                while j < len(s):
                    if s[j] == "\\":
                        j += 2
                        continue
                    if s[j] == "$":
                        break
                    j += 1
                out += keep(self.math_inline(s[i + 1:j]))
                i = j + 1
                continue
            out += c
            i += 1
        return out

    def _ref_target(self, label: str) -> tuple[str, str]:
        """Return (href, text) for a \\ref to `label`."""
        info = self.labels.get(label)
        if not info:
            self.warnings.append("unknown label " + label)
            return "#", "??"
        node = self.node_of_label.get(label)
        num = info["num"]
        if info["type"] == "equation":
            href = "#eq/%s" % label
        elif info["type"] == "figure":
            href = "#fig/%s" % label
        elif node:
            href = "#%s" % node
        else:
            href = "#"
        return href, num

    def _commands(self, s: str, keep, stash: list) -> str:
        nested = lambda t: self._inline(t, stash)
        # theorem-like references: "Theorem~\ref{..}" (also "Sections~\ref{a}--\ref{b}")
        def word_ref(m):
            word, plural, label = m.group(1), m.group(2), m.group(3)
            href, num = self._ref_target(label)
            return keep('<a class="ref" href="%s" data-label="%s">%s%s&nbsp;%s</a>' % (href, html.escape(label), word, plural, num))
        s = re.sub(r"\b(" + "|".join(REF_WORDS) + r")(s?)~\\ref\*?\{([^}]*)\}", word_ref, s)

        def secref(m):
            kind, label = m.group(1), m.group(2)
            href, num = self._ref_target(label)
            word = "Section" if kind == "Secref" else "Appendix"
            return keep('<a class="ref ref-section" href="%s" data-label="%s"><strong>%s&nbsp;%s</strong></a>' % (href, html.escape(label), word, num))
        s = re.sub(r"\\(Secref|Appref)\{([^}]*)\}", secref, s)

        def eqref(m):
            label = m.group(1)
            href, num = self._ref_target(label)
            return keep('<a class="ref ref-eq" href="%s" data-label="%s">(%s)</a>' % (href, html.escape(label), num))
        s = re.sub(r"\\eqref\{([^}]*)\}", eqref, s)

        def plainref(m):
            label = m.group(1)
            href, num = self._ref_target(label)
            return keep('<a class="ref" href="%s" data-label="%s">%s</a>' % (href, html.escape(label), num))
        s = re.sub(r"\\ref\*?\{([^}]*)\}", plainref, s)

        def hyperref(m):
            label, text = m.group(1), m.group(2)
            href, _ = self._ref_target(label)
            return keep('<a class="ref" href="%s" data-label="%s">%s</a>' % (href, html.escape(label), nested(text)))
        s = re.sub(r"\\hyperref\[([^\]]*)\]\{((?:[^{}]|\{[^{}]*\})*)\}", hyperref, s)

        def cite(m):
            opt, keys = m.group(1), m.group(2)
            parts = []
            for key in [k.strip() for k in keys.split(",")]:
                info = self.bibkeys.get(key)
                if not info:
                    self.warnings.append("unknown citation key " + key)
                    parts.append('<a class="cite" href="#bib" data-key="%s">?</a>' % html.escape(key))
                    continue
                parts.append('<a class="cite" href="#bib/%s" data-key="%s" title="%s">%d</a>' % (
                    html.escape(key), html.escape(key), html.escape(info["text"], quote=True), info["num"]))
            parts.sort(key=lambda p: int(re.search(r">(\d+|\?)<", p).group(1)) if re.search(r">(\d+)<", p) else 10**6)
            text = ", ".join(parts)
            if opt:
                text += ", " + nested(opt)
            return keep("[%s]" % text)
        s = re.sub(r"\\cite(?:\[((?:[^\]])*)\])?\{([^}]*)\}", cite, s)

        def href(m):
            url, text = m.group(1), m.group(2)
            return keep('<a class="ext" href="%s" target="_blank" rel="noopener">%s</a>' % (html.escape(url, quote=True), nested(text)))
        s = re.sub(r"\\href\{([^}]*)\}\{((?:[^{}]|\{[^{}]*\})*)\}", href, s)

        def url(m):
            u = m.group(1)
            return keep('<a class="ext" href="%s" target="_blank" rel="noopener">%s</a>' % (html.escape(u, quote=True), html.escape(u)))
        s = re.sub(r"\\url\{([^}]*)\}", url, s)

        def footnote(m):
            return keep('<span class="footnote"><button type="button" class="fn-mark" aria-label="Footnote">*</button><span class="fn-body" role="note">%s</span></span>' % nested(m.group(1)))
        s = re.sub(r"\\footnote\{((?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\}", footnote, s)

        # formatting commands with one argument
        simple = {
            "emph": ("em", ""), "textit": ("em", ""), "textbf": ("strong", ""), "texttt": ("code", ""),
            "textup": ("span", ' class="upright"'), "textsc": ("span", ' class="smallcaps"'),
            "textnormal": ("span", ""), "textrm": ("span", ""), "mbox": ("span", ' class="nowrap"'),
        }
        for _ in range(4):  # nested formatting
            def fmt(m):
                cmd, arg = m.group(1), m.group(2)
                tag, attrs = simple[cmd]
                return keep("<%s%s>%s</%s>" % (tag, attrs, nested(arg), tag))
            s2 = re.sub(r"\\(" + "|".join(simple) + r")\{((?:[^{}]|\{[^{}]*\})*)\}", fmt, s)
            if s2 == s:
                break
            s = s2
        s = re.sub(r"\\textcolor\{[^}]*\}\{((?:[^{}]|\{[^{}]*\})*)\}", lambda m: m.group(1), s)
        s = re.sub(r"\\texorpdfstring\{((?:[^{}]|\{[^{}]*\})*)\}\{(?:[^{}]|\{[^{}]*\})*\}", lambda m: m.group(1), s)
        s = re.sub(r"\{\\(em|it|bf)\s+((?:[^{}]|\{[^{}]*\})*)\}", lambda m: keep("<%s>%s</%s>" % ("em" if m.group(1) != "bf" else "strong", nested(m.group(2)), "em" if m.group(1) != "bf" else "strong")), s)
        s = re.sub(r"\\label\{([^}]*)\}", lambda m: keep('<span class="anchor" id="%s"></span>' % html.escape(m.group(1))), s)
        # remove layout commands
        s = re.sub(r"\\(smallskip|medskip|bigskip|noindent|centering|FloatBarrier|newpage|clearpage|par|relax|linewidth|scriptsize|footnotesize|small|normalsize|large|itshape|bfseries)\b", " ", s)
        s = re.sub(r"\\(thispagestyle|vspace\*?|hspace\*?|setlist|pagestyle|includegraphics|caption)\{[^}]*\}", " ", s)
        s = re.sub(r"\\setlist\[[^\]]*\]\{[^}]*\}", " ", s)
        s = re.sub(r"\\\\(\[[^\]]*\])?", keep("<br>"), s)
        return s

    def _typography(self, s: str) -> str:
        s = apply_accents(s)
        s = s.replace("\\,", "\u2009").replace("\\ ", " ").replace("\\@", "").replace("\\-", "")
        s = s.replace("\\&", "&").replace("\\%", "%").replace("\\$", "$").replace("\\_", "_").replace("\\#", "#")
        s = s.replace("\\{", "{").replace("\\}", "}")
        s = re.sub(r"\\textendash\b", "–", s)
        s = s.replace("---", "—").replace("--", "–")
        s = s.replace("``", "“").replace("''", "”").replace("`", "‘").replace("'", "’")
        s = s.replace("~", "\u00a0")
        s = s.replace("\\ldots", "…").replace("\\dots", "…")
        # collect unknown commands for the report, then drop the backslash
        for m in re.finditer(r"\\([A-Za-z]+)", s):
            self.unknown_cmds[m.group(1)] = self.unknown_cmds.get(m.group(1), 0) + 1
        s = re.sub(r"\\([A-Za-z]+)\s*", lambda m: m.group(1) if m.group(1) in ("i", "l") else "", s)
        s = re.sub(r"(?<!\\)[{}]", "", s)
        return s


# --------------------------------------------------------------------------- document structure


def parse_document(body: str):
    """Return the ordered list of top-level blocks of the document body."""
    blocks = []
    pat = re.compile(
        r"\\(section|subsection)\*?\{|\\begin\{(" + "|".join(THEOREM_ENVS) + r"|proof|figure|abstract)\}|\\appendix\b|"
        r"\\maketitle|\\thispagestyle\{[^}]*\}|\\bibliographystyle\{[^}]*\}|\\bibliography\{[^}]*\}|\\begin\{minipage\}|\\setlist\[[^\]]*\]\{[^}]*\}"
    )
    i = 0
    while True:
        m = pat.search(body, i)
        if not m:
            tail = body[i:]
            if tail.strip():
                blocks.append({"type": "prose", "tex": tail, "start": i})
            break
        if m.start() > i and body[i:m.start()].strip():
            blocks.append({"type": "prose", "tex": body[i:m.start()], "start": i})
        tok = m.group(0)
        if m.group(1):  # section / subsection
            title, after = read_group(body, m.end() - 1)
            lab = re.match(r"\s*\\label\{([^}]*)\}", body[after:])
            label = lab.group(1) if lab else None
            if lab:
                after += lab.end()
            blocks.append({"type": m.group(1), "title": title, "label": label, "start": m.start()})
            i = after
        elif m.group(2):
            env = m.group(2)
            opt, k = read_opt(body, m.end())
            body_end, after = find_env_end(body, env, k)
            content = body[k:body_end]
            lab = re.match(r"\s*\\label\{([^}]*)\}", content)
            label = lab.group(1) if lab else None
            if lab:
                content = content[lab.end():]
            blocks.append({"type": "env", "env": env, "opt": opt, "label": label, "tex": content, "start": m.start(), "end": after})
            i = after
        elif tok == "\\appendix":
            blocks.append({"type": "appendix", "start": m.start()})
            i = m.end()
        elif tok.startswith("\\bibliography"):
            break  # end matter: bibliography and addresses are not part of the text
        elif tok == "\\begin{minipage}":
            body_end, after = find_env_end(body, "minipage", m.end())
            blocks.append({"type": "skip", "start": m.start()})
            i = after
        else:
            blocks.append({"type": "skip", "start": m.start()})
            i = m.end()
    return blocks


def number_everything(body: str, blocks: list) -> dict:
    """Assign printed numbers to sections, theorem-like environments, equations and figures."""
    labels: dict[str, dict] = {}
    numbers: dict[str, str] = {}
    sec = 0
    appendix = False
    subsec = 0
    thm = 0
    eq = 0
    fig = 0
    sec_name = ""

    def secstr():
        return sec_name

    # equations are numbered in textual order across the whole body, so scan the body directly
    eq_pat = re.compile(r"\\section\*?\{|\\appendix\b|\\begin\{equation\}|\\begin\{align\}|\\begin\{(" + "|".join(THEOREM_ENVS) + r")\}|\\begin\{figure\}|\\subsection\{")
    i = 0
    while True:
        m = eq_pat.search(body, i)
        if not m:
            break
        tok = m.group(0)
        if tok.startswith("\\section"):
            if appendix:
                sec += 1
                sec_name = chr(ord("A") + sec - 1)
            else:
                sec += 1
                sec_name = str(sec)
            subsec = thm = eq = fig = 0
            title, after = read_group(body, m.end() - 1)
            lab = re.match(r"\s*\\label\{([^}]*)\}", body[after:])
            if lab:
                labels[lab.group(1)] = {"type": "section", "num": secstr(), "title": title}
                numbers[lab.group(1)] = secstr()
            labels["__section_%d" % m.start()] = {"type": "section", "num": secstr(), "title": title}
            i = after
        elif tok.startswith("\\subsection"):
            subsec += 1
            title, after = read_group(body, m.end() - 1)
            lab = re.match(r"\s*\\label\{([^}]*)\}", body[after:])
            num = "%s.%d" % (secstr(), subsec)
            if lab:
                labels[lab.group(1)] = {"type": "subsection", "num": num, "title": title}
                numbers[lab.group(1)] = num
            i = after
        elif tok == "\\appendix":
            appendix = True
            sec = 0
            i = m.end()
        elif tok == "\\begin{equation}":
            body_end, after = find_env_end(body, "equation", m.end())
            content = body[m.end():body_end]
            lab = re.search(r"\\label\{([^}]*)\}", content)
            tag = re.search(r"\\tag\{([^}]*)\}", content)
            if tag:
                num = tag.group(1)
            else:
                eq += 1
                num = "%s.%d" % (secstr(), eq)
            if lab:
                labels[lab.group(1)] = {"type": "equation", "num": num}
                numbers[lab.group(1)] = num
            i = after
        elif tok == "\\begin{align}":
            body_end, after = find_env_end(body, "align", m.end())
            content = body[m.end():body_end]
            for row in split_top_level(content):
                if not row.strip():
                    continue
                if re.search(r"\\notag|\\nonumber", row):
                    continue
                eq += 1
                num = "%s.%d" % (secstr(), eq)
                lab = re.search(r"\\label\{([^}]*)\}", row)
                if lab:
                    labels[lab.group(1)] = {"type": "equation", "num": num}
                    numbers[lab.group(1)] = num
            i = after
        elif tok == "\\begin{figure}":
            body_end, after = find_env_end(body, "figure", m.end())
            content = body[m.end():body_end]
            fig += 1
            num = "%s.%d" % (secstr(), fig)
            lab = re.search(r"\\label\{([^}]*)\}", content)
            if lab:
                labels[lab.group(1)] = {"type": "figure", "num": num}
                numbers[lab.group(1)] = num
            i = after
        else:  # theorem-like
            env = m.group(1)
            thm += 1
            num = "%s.%d" % (secstr(), thm)
            opt, k = read_opt(body, m.end())
            lab = re.match(r"\s*\\label\{([^}]*)\}", body[k:])
            key = lab.group(1) if lab else "__%s_%d" % (env, m.start())
            labels[key] = {"type": env, "num": num, "start": m.start()}
            numbers[key] = num
            i = k
    return {"labels": labels, "numbers": numbers}


def check_against_aux(labels: dict, aux_path: pathlib.Path) -> list[str]:
    msgs = []
    if not aux_path or not aux_path.exists():
        return ["(no .aux file given; numbering not cross-checked)"]
    aux = aux_path.read_text(encoding="utf-8", errors="replace")
    for m in re.finditer(r"\\newlabel\{([^}@]*)\}\{\{([^}]*)\}", aux):
        lab, num = m.group(1), m.group(2).strip("{}")
        if lab in labels and labels[lab]["num"] != num:
            msgs.append("MISMATCH %s: tex-computed %s vs aux %s" % (lab, labels[lab]["num"], num))
    if not msgs:
        msgs.append("numbering agrees with %s for all labels" % aux_path.name)
    return msgs


# --------------------------------------------------------------------------- bibliography


def parse_bbl(bbl_text: str, conv: Converter) -> list[dict]:
    items = []
    bbl_text = strip_comments(bbl_text)
    for m in re.finditer(r"\\bibitem\{([^}]*)\}(.*?)(?=\\bibitem\{|\\end\{thebibliography\})", bbl_text, re.S):
        key, text = m.group(1), m.group(2)
        text = text.replace("\\newblock", " ")
        text = re.sub(r"\s+", " ", text).strip()
        items.append({"key": key, "tex": text})
    for n, it in enumerate(items, 1):
        it["num"] = n
        it["html"] = conv.inline(it["tex"])
        plain = re.sub(r"<[^>]+>", "", it["html"])
        it["text"] = html.unescape(plain)
    return items


def parse_bib_links(bib_text: str) -> dict:
    links = {}
    for m in re.finditer(r"@\w+\{([^,]+),(.*?)\n\}", bib_text, re.S):
        key, body = m.group(1).strip(), m.group(2)
        doi = re.search(r"\bdoi\s*=\s*[{\"]([^}\"]+)", body, re.I)
        url = re.search(r"\burl\s*=\s*[{\"]([^}\"]+)", body, re.I)
        arx = re.search(r"arXiv[: ]\s*(\d{4}\.\d{4,5})", body)
        if doi:
            links[key] = "https://doi.org/" + doi.group(1).strip()
        elif url:
            links[key] = url.group(1).strip()
        elif arx:
            links[key] = "https://arxiv.org/abs/" + arx.group(1)
    return links


# --------------------------------------------------------------------------- build


def find_text(body: str, start_snippet: str, end_snippet: str, occurrence: int = 1) -> tuple[int, int]:
    """Locate a TeX range by its first and last words (whitespace-insensitive)."""
    def loc(snippet, from_pos):
        pat = re.compile(r"\s+".join(re.escape(w) for w in snippet.split()))
        m = pat.search(body, from_pos)
        if not m:
            raise ValueError("anchor not found: %r" % snippet)
        return m
    pos = 0
    for _ in range(occurrence):
        m1 = loc(start_snippet, pos)
        pos = m1.end()
    m2 = loc(end_snippet, m1.start())
    return m1.start(), m2.end()


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--tex", default=str(HERE / "source" / "v7.tex"))
    ap.add_argument("--bbl", default=str(HERE / "source" / "v7.bbl"))
    ap.add_argument("--bib", default=str(HERE / "source" / "refs-v7.bib"), help=".bib for DOI / URL links (optional)")
    ap.add_argument("--aux", default=None, help="optional .aux to cross-check numbering")
    ap.add_argument("--out", default=str(HERE / "data.js"))
    args = ap.parse_args(argv)

    tex = strip_comments(pathlib.Path(args.tex).read_text(encoding="utf-8"))
    body = tex.split("\\begin{document}", 1)[1].split("\\end{document}", 1)[0]
    meta = json.loads((HERE / "content" / "meta.json").read_text(encoding="utf-8"))
    spec = json.loads((HERE / "content" / "nodes.json").read_text(encoding="utf-8"))

    blocks = parse_document(body)
    numbering = number_everything(body, blocks)
    labels, numbers = numbering["labels"], numbering["numbers"]
    aux_msgs = check_against_aux(labels, pathlib.Path(args.aux)) if args.aux else ["(no .aux given)"]

    # bibliography
    conv = Converter(numbers, labels, {}, {})
    bbl_items = parse_bbl(pathlib.Path(args.bbl).read_text(encoding="utf-8"), conv)
    bib_links = parse_bib_links(pathlib.Path(args.bib).read_text(encoding="utf-8", errors="replace")) if args.bib and pathlib.Path(args.bib).exists() else {}
    for it in bbl_items:
        it["url"] = bib_links.get(it["key"])
    conv.bibkeys = {it["key"]: it for it in bbl_items}

    # which node displays which label (for cross-reference links)
    node_of_label: dict[str, str] = {}
    for nd in spec["nodes"]:
        for lab in nd.get("labels", []) + ([nd["label"]] if nd.get("label") else []):
            node_of_label.setdefault(lab, nd["id"])
    # sections own their own labels and their subsections'
    conv.node_of_label = node_of_label

    # index theorem-like blocks by label / by nth occurrence
    env_blocks = [b for b in blocks if b["type"] == "env" and b["env"] in THEOREM_ENVS]
    proof_after: dict[int, dict] = {}
    for idx, b in enumerate(blocks):
        if b["type"] == "env" and b["env"] in THEOREM_ENVS:
            # the proof is the next env block named proof, if it comes before another theorem-like env
            for c in blocks[idx + 1:]:
                if c["type"] == "env" and c["env"] == "proof":
                    proof_after[b["start"]] = c
                    break
                if c["type"] == "env" and c["env"] in THEOREM_ENVS or c["type"] in ("section",):
                    break

    def env_by_label(label):
        for b in env_blocks:
            if b["label"] == label:
                return b
        raise KeyError(label)

    def env_nth(env, nth):
        c = 0
        for b in env_blocks:
            if b["env"] == env:
                c += 1
                if c == nth:
                    return b
        raise KeyError((env, nth))

    # section blocks: group top-level blocks by section
    sections = []
    cur = None
    appendix = False
    for b in blocks:
        if b["type"] == "appendix":
            appendix = True
            continue
        if b["type"] == "section":
            cur = {"title": b["title"], "label": b["label"], "blocks": [], "appendix": appendix,
                   "num": labels["__section_%d" % b["start"]]["num"]}
            sections.append(cur)
            continue
        if cur is not None:
            cur["blocks"].append(b)
        else:
            # front matter: abstract lives here
            if b["type"] == "env" and b["env"] == "abstract":
                meta["abstractHtml"] = None
                meta["_abstract_tex"] = b["tex"]

    nodes: dict[str, dict] = {}
    order: list[str] = []

    def section_node_id(label, title=None):
        for nd in spec["nodes"]:
            if nd.get("kind") != "section":
                continue
            if label and nd.get("label") == label:
                return nd["id"]
            if title and nd.get("sectionTitle") and nd["sectionTitle"].strip() == title.strip():
                return nd["id"]
        return None

    def convert_written(node, nd):
        """Hand-written fields (summaries, proof ideas, notes) are TeX too."""
        for src, dst in (("summaryTex", "summaryHtml"), ("ideaTex", "ideaHtml"), ("noteTex", "noteHtml")):
            if nd.get(src):
                node[dst] = conv.prose(nd[src])
                node.pop(src, None)
        if nd.get("lean"):
            node["lean"] = [dict(l, noteHtml=conv.inline(l.get("note", "")), url=meta["repoUrl"] + "/blob/main/" + l["file"]) for l in nd["lean"]]
            for l in node["lean"]:
                l.pop("note", None)
        if nd.get("cites"):
            node["citations"] = []
            for key in nd["cites"]:
                it = conv.bibkeys.get(key)
                if it:
                    node["citations"].append({"key": key, "num": it["num"], "html": it["html"], "url": it.get("url")})
                else:
                    conv.warnings.append("external node %s cites unknown key %s" % (nd["id"], key))

    # ---- first pass: theorem-like nodes (statement + proof) --------------------------------
    for nd in spec["nodes"]:
        node = dict(nd)
        node.setdefault("uses", [])
        node.setdefault("figures", [])
        kind = nd["kind"]
        conv.current_node = nd["id"]
        from_env = kind in THEOREM_ENVS and (nd.get("env") or (nd.get("label") and labels.get(nd["label"], {}).get("type") in THEOREM_ENVS))
        if from_env:
            b = env_by_label(nd["label"]) if nd.get("label") else env_nth(nd["env"], nd["nth"])
            key = nd.get("label") or "__%s_%d" % (b["env"], b["start"])
            node["number"] = "%s %s" % (KIND_LABEL[b["env"]], numbers[key])
            node["numberOnly"] = numbers[key]
            node["statementHtml"] = conv.prose(b["tex"])
            node["sourceLine"] = tex[:tex.index(body) + b["start"]].count("\n") + 1
            pf = proof_after.get(b["start"])
            if pf is not None:
                node["proofHtml"] = conv.prose(pf["tex"])
            for lab in [nd.get("label")] + nd.get("labels", []):
                if lab:
                    node_of_label.setdefault(lab, nd["id"])
        elif kind == "section":
            pass  # second pass
        elif kind in ("definition", "estimate", "example", "claim", "background", "remark", "figure"):
            if "extract" in nd:
                parts = []
                for ex in (nd["extract"] if isinstance(nd["extract"], list) else [nd["extract"]]):
                    a, z = find_text(body, ex["from"], ex["to"], ex.get("occurrence", 1))
                    parts.append(body[a:z])
                    node["sourceLine"] = tex[:tex.index(body) + a].count("\n") + 1
                node["statementHtml"] = "\n".join(conv.prose(p) for p in parts)
            if "proofExtract" in nd:
                ex = nd["proofExtract"]
                a, z = find_text(body, ex["from"], ex["to"], ex.get("occurrence", 1))
                node["proofHtml"] = conv.prose(body[a:z])
        elif kind == "external":
            pass
        convert_written(node, nd)
        if nd.get("number"):
            node["number"] = nd["number"]
        nodes[nd["id"]] = node
        order.append(nd["id"])

    # ---- figures ---------------------------------------------------------------------------
    fig_blocks = [b for b in blocks if b["type"] == "env" and b["env"] == "figure"]
    figures = {}
    for b in fig_blocks:
        lab = re.search(r"\\label\{([^}]*)\}", b["tex"])
        cap = re.search(r"\\caption\{", b["tex"])
        caption_tex = read_group(b["tex"], cap.end() - 1)[0] if cap else ""
        imgs = re.findall(r"\\includegraphics(?:\[[^\]]*\])?\{([^}]*)\}", b["tex"])
        key = lab.group(1) if lab else "fig_%d" % b["start"]
        figures[key] = {"label": key, "num": numbers.get(key, "?"), "captionHtml": conv.inline(caption_tex), "sources": imgs}
    for nd in spec["nodes"]:
        if nd["kind"] == "figure":
            node = nodes[nd["id"]]
            node["number"] = nd.get("number") or ("Figure %s" % ", ".join(numbers[l] for l in nd["labels"]))
            node["figureBlocks"] = []
            for fl in nd["labels"]:
                f = dict(figures[fl])
                f.update(spec.get("figureAssets", {}).get(fl, {}))
                node["figureBlocks"].append(f)
                node_of_label.setdefault(fl, nd["id"])

    # ---- sections --------------------------------------------------------------------------
    sec_nodes = {}
    for s in sections:
        sid = section_node_id(s["label"], s["title"])
        if not sid:
            conv.warnings.append("no section node for section %r" % s["title"])
            continue
        conv.current_node = sid
        node = nodes[sid]
        node["number"] = ("Appendix %s" if s["appendix"] else "Section %s") % s["num"]
        node["numberOnly"] = s["num"]
        node["paperTitle"] = conv.inline(s["title"])
        node_of_label.setdefault(s["label"], sid)
        parts = []
        for b in s["blocks"]:
            if b["type"] == "prose":
                parts.append(conv.prose(b["tex"]))
            elif b["type"] == "subsection":
                num = labels.get(b["label"], {}).get("num", "")
                parts.append('<h3 class="subsection" id="%s"><span class="subsection__num">%s</span> %s</h3>' % (
                    html.escape(b["label"] or ""), num, conv.inline(b["title"])))
                if b["label"]:
                    node_of_label.setdefault(b["label"], sid)
            elif b["type"] == "env" and b["env"] in THEOREM_ENVS:
                key = b["label"] or "__%s_%d" % (b["env"], b["start"])
                target = node_of_label.get(b["label"]) if b["label"] else None
                if not target:
                    for nd in spec["nodes"]:
                        if nd.get("env") == b["env"] and nd.get("nth") and env_nth(b["env"], nd["nth"]) is b:
                            target = nd["id"]
                title = nodes[target]["title"] if target else ""
                parts.append(
                    '<div class="result-card" data-node="%s"><div class="result-card__head"><span class="result-card__num">%s %s</span>'
                    '<span class="result-card__title">%s</span>%s</div><div class="result-card__body">%s</div></div>' % (
                        html.escape(target or ""), KIND_LABEL[b["env"]], numbers[key], html.escape(title),
                        ('<a class="result-card__open" href="#%s">Open with proof</a>' % target) if target else "",
                        conv.prose(b["tex"])))
            elif b["type"] == "env" and b["env"] == "proof":
                parts.append('<details class="proof-inline"><summary>Proof</summary>%s</details>' % conv.prose(b["tex"]))
            elif b["type"] == "env" and b["env"] == "figure":
                lab = re.search(r"\\label\{([^}]*)\}", b["tex"])
                key = lab.group(1) if lab else None
                target = node_of_label.get(key) if key else None
                parts.append('<div class="figure-slot" data-figure="%s" data-node="%s"></div>' % (html.escape(key or ""), html.escape(target or "")))
        node["bodyHtml"] = "\n".join(parts)
        sec_nodes[sid] = node

    # abstract and other hand-written meta text
    conv.current_node = None
    meta["abstractHtml"] = conv.prose(meta.pop("_abstract_tex", ""))
    for k in list(meta.keys()):
        if k.endswith("Tex"):
            meta[k[:-3] + "Html"] = conv.inline(meta.pop(k))
    notation = []
    for item in spec.get("notation", []):
        notation.append({"sym": item["sym"], "textHtml": conv.inline(item["text"]), "node": item.get("node")})

    # where a node sits in the paper, e.g. "§1.2" or "Appendix B"
    for nid in order:
        nd = nodes[nid]
        if nd["kind"] in ("section", "external"):
            continue
        if nd.get("subsection") and nd["subsection"] in labels:
            nd["where"] = "§" + labels[nd["subsection"]]["num"]
        elif nd.get("parent") in nodes:
            p = nodes[nd["parent"]]
            nd["where"] = ("Appendix " + p["numberOnly"]) if p["number"].startswith("Appendix") else "§" + p["numberOnly"]
    # children / parent bookkeeping
    for nid in order:
        nodes[nid].setdefault("children", [])
    for nid in order:
        p = nodes[nid].get("parent")
        if p and p in nodes and nid not in nodes[p]["children"]:
            nodes[p]["children"].append(nid)

    # ---- edges & used-by -----------------------------------------------------------------------
    edges = []
    for nid in order:
        for u in nodes[nid].get("uses", []):
            src = u if isinstance(u, str) else u["id"]
            note = None if isinstance(u, str) else u.get("note")
            if src not in nodes:
                conv.warnings.append("edge from unknown node %s (used by %s)" % (src, nid))
                continue
            edges.append({"from": src, "to": nid, "note": note})
    for nid in order:
        nodes[nid]["usedBy"] = [e["from"] if False else e["to"] for e in edges if e["from"] == nid]
        nodes[nid]["usesIds"] = [e["from"] for e in edges if e["to"] == nid]
    for nid in order:
        nodes[nid].pop("uses", None)
        nodes[nid]["uses"] = nodes[nid].pop("usesIds")

    # where each equation label is displayed
    eq_index = {}
    for lab, info in labels.items():
        if info["type"] == "equation":
            eq_index[lab] = {"num": info["num"], "nodes": conv.eq_seen.get(lab, [])}

    label_index = {}
    for lab, info in labels.items():
        if lab.startswith("__"):
            continue
        label_index[lab] = {"type": info["type"], "num": info["num"], "node": node_of_label.get(lab),
                            "nodes": conv.eq_seen.get(lab, [])}

    data = {
        "meta": meta,
        "order": order,
        "nodes": nodes,
        "edges": edges,
        "bibliography": [{k: v for k, v in it.items() if k != "tex"} for it in bbl_items],
        "labels": label_index,
        "notation": notation,
        "kinds": spec.get("kinds", {}),
    }
    out = pathlib.Path(args.out)
    out.write_text("// Generated by site/build.py from %s — do not edit by hand.\nwindow.PAPER = %s;\n" % (
        pathlib.Path(args.tex).name, json.dumps(data, ensure_ascii=False, indent=1)), encoding="utf-8")

    # ---- report ----------------------------------------------------------------------------
    print("wrote %s (%d nodes, %d edges, %d bibliography items)" % (out, len(nodes), len(edges), len(bbl_items)))
    for m in aux_msgs:
        print("  " + m)
    unknown = {k: v for k, v in conv.unknown_cmds.items()}
    if unknown:
        print("  commands dropped from text: " + ", ".join("\\%s(%d)" % kv for kv in sorted(unknown.items())))
    for w in sorted(set(conv.warnings)):
        print("  WARNING " + w)
    return 0


if __name__ == "__main__":
    sys.exit(main())
