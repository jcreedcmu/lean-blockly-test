import { tryReplace } from '../src/abbreviations';

describe('tryReplace', () => {
  test('"prov" rewrites to "∏v"', () => {
    expect(tryReplace('prov')).toBe('∏v');
  });

  test('"prod" rewrites to "∏"', () => {
    expect(tryReplace('prod')).toBe('∏');
  });

  test('"pro" does not rewrite (ambiguous prefix)', () => {
    expect(tryReplace('pro')).toBeUndefined();
  });

  test('"a" does not rewrite (ambiguous prefix)', () => {
    expect(tryReplace('a')).toBeUndefined();
  });

  test('"a " rewrites to "α "', () => {
    expect(tryReplace('a ')).toBe('α ');
  });
});
