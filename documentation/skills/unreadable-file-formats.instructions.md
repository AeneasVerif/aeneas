# Skill: Handling Unreadable File Formats

## Critical Rule

**If the user asks you to read or use a file and you cannot actually read it (e.g., a PDF, a binary file, an image with embedded text), say so immediately and upfront.** Do NOT silently rely on training knowledge or guess the content. Be explicit about what you can and cannot access.

### Examples

- User: "Read the FIPS 203 PDF and formalize the algorithms"
  - ✅ Correct: "I cannot read PDF files directly. Let me install pymupdf to extract the text, or you can provide the relevant sections."
  - ❌ Wrong: Silently writing code based on training knowledge without disclosing you didn't read the PDF.

- User: "Check the spec in spec.pdf"
  - ✅ Correct: "I can't read PDFs natively. I can install pymupdf to extract the text — shall I?"
  - ❌ Wrong: Pretending to have read it, or guessing the content.

## Reading PDFs with `pdftohtml -xml`

Use poppler's `pdftohtml` to extract PDF content as XML. The XML output contains
per-span font size, position (top/left), and width — enough for an agent to
interpret superscripts, subscripts, and indentation directly.

**Requirement:** `pdftohtml` from poppler (install with `brew install poppler`
on macOS, `apt install poppler-utils` on Linux).

### Usage

```bash
pdftohtml -xml -f <start_page> -l <end_page> -stdout file.pdf
```
Pages are 1-indexed. Extract a few pages at a time to keep token cost manageable.

### How to read the XML

The output contains `<fontspec>` declarations and `<text>` spans:
```xml
<fontspec id="5" size="18" family="LatinModernMath" color="#000000"/>
<fontspec id="7" size="13" family="LatinModernMath" color="#000000"/>
<text top="273" left="147" width="21" height="15" font="2">for</text>
<text top="309" left="266" width="38" font="12">BitRev</text>
```

**Interpreting the spans:**
- **Font size** distinguishes baseline text from super/subscripts. The baseline
  font is typically the most common size (e.g., size 18). Spans with smaller size
  (e.g., size 13) are superscripts or subscripts.
- **`top` position** distinguishes superscript from subscript: smaller `top` =
  higher on page = superscript; larger `top` = lower = subscript. Compare against
  the `top` of baseline-sized spans on the same line.
- **`left` position** encodes indentation. Deeper nesting = larger `left` value.
  This is critical for reading algorithm pseudocode with nested loops.
- **`width="0"`** spans are combining characters (e.g., hat `̂`, tilde). They
  modify the previous character but carry no width.

### Quality notes

- **Greek letters** (θ, ρ, π, χ, ι, ζ): ✅ Preserved in Unicode
- **Math symbols** (⊕, ≤, ⋅, ∈): ✅ Preserved in Unicode
- **Superscripts/subscripts**: ✅ Detectable via font size + top position
- **Indentation**: ✅ Encoded in `left` coordinates
- **Algorithm pseudocode**: ✅ All information present (nesting, line numbers)
- **Tables**: ⚠️ May require careful `left`-position grouping
- **Figures/diagrams**: ❌ Not extractable as text

### Fallback: pdftotext -layout

When you just need readable text without super/subscript detection:
```bash
pdftotext -layout file.pdf - | sed -n '100,200p'
```
Preserves indentation but loses font-size metadata.

### When poppler is not available

If poppler is not installed, offer alternatives:
1. Install poppler: `brew install poppler` (macOS) or `apt install poppler-utils` (Linux)
2. User pastes relevant sections into the chat
3. User converts PDF to text themselves
4. Look for HTML versions of the same document (e.g., IETF drafts on datatracker.ietf.org)

## General principle

**Transparency over convenience.** It is always better to tell the user "I cannot read this file" than to silently fabricate or guess content. This applies to:
- PDF files
- Binary files (`.bin`, `.dat`, compiled objects)
- Images with text (`.png`, `.jpg` of documents)
- Encrypted or password-protected files
- Files in formats you have no parser for
