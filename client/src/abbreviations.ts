import { AbbreviationProvider } from '@leanprover/unicode-input';

const abbreviationProvider = new AbbreviationProvider({
  abbreviationCharacter: '\\',
  customTranslations: {},
  eagerReplacementEnabled: true,
});

const allAbbreviationKeys = Object.keys(abbreviationProvider.getSymbolsByAbbreviation());

/**
 * Given text after a `\`, check whether it unambiguously resolves to a
 * replacement. Returns the replacement string, or undefined if the text
 * is still ambiguous (could extend to a longer abbreviation).
 *
 * The rule: rewrite when no abbreviation key is strictly longer than
 * `text` and starts with `text`. This fires when:
 *  - `text` is an exact abbreviation with no longer extensions (e.g. `prod`)
 *  - `text` has gone past all valid abbreviations (e.g. `prov`, `a `)
 */
export function tryReplace(text: string): string | undefined {
  const hasLongerPrefix = allAbbreviationKeys.some(
    k => k.length > text.length && k.startsWith(text)
  );
  if (hasLongerPrefix) return undefined;
  return abbreviationProvider.getReplacementText(text);
}

/**
 * Attach to an HTMLInputElement so that typing e.g. `\alpha` immediately
 * rewrites to `α` once the abbreviation is unambiguous.
 */
export function attachAbbreviationRewriter(input: HTMLInputElement): void {
  let replacing = false;
  input.addEventListener('input', () => {
    if (replacing) return;
    const pos = input.selectionStart;
    if (pos === null) return;
    const text = input.value;
    const before = text.slice(0, pos);
    const bsIdx = before.lastIndexOf('\\');
    if (bsIdx === -1) return;
    const abbrev = before.slice(bsIdx + 1);
    const replacement = tryReplace(abbrev);
    if (replacement === undefined) return;
    const newText = text.slice(0, bsIdx) + replacement + text.slice(pos);
    input.value = newText;
    const newPos = bsIdx + replacement.length;
    input.setSelectionRange(newPos, newPos);
    replacing = true;
    input.dispatchEvent(new Event('input', { bubbles: true }));
    replacing = false;
  });
}
