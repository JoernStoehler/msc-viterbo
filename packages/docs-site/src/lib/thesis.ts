import path from 'node:path';
import type { AstroComponentFactory, MarkdownInstance } from 'astro';

export interface FigureMeta {
  id: string;
  title?: string;
  caption?: string;
  assets: {
    interactive?: string;
    static: string;
  };
}

export interface ThesisFrontmatter {
  title: string;
  slug?: string;
  summary?: string;
  order?: number;
  internal?: boolean;
  figures?: FigureMeta[];
}

export interface ThesisEntry {
  slug: string;
  title: string;
  summary?: string;
  order: number;
  figures: FigureMeta[];
  Content: AstroComponentFactory;
  file: string;
}

type ThesisModule = MarkdownInstance<ThesisFrontmatter>;

const thesisModules = import.meta.glob<ThesisModule>(
  '../content/thesis/**/*.mdx',
  { eager: true },
);

const thesisEntries: ThesisEntry[] = Object.entries(thesisModules).map(([filePath, module]) => {
  const frontmatter = module.frontmatter ?? ({} as ThesisFrontmatter);
  const slug = frontmatter.slug || deriveSlug(filePath);
  return {
    slug,
    title: frontmatter.title ?? deriveTitle(filePath),
    summary: frontmatter.summary,
    order: frontmatter.order ?? 0,
    figures: frontmatter.figures ?? [],
    Content: module.default,
    file: filePath,
  };
}).filter((entry) => {
  const fm = thesisModules[entry.file]?.frontmatter as ThesisFrontmatter | undefined;
  return !(fm && fm.internal);
});

function deriveSlug(filePath: string): string {
  const fileName = path.basename(filePath, path.extname(filePath));
  return fileName.replace(/^\d+-/, '');
}

function deriveTitle(filePath: string): string {
  const slug = deriveSlug(filePath);
  return slug.replace(/-/g, ' ').replace(/\b\w/g, (ch) => ch.toUpperCase());
}

export function getAllThesisEntries(): ThesisEntry[] {
  return [...thesisEntries].sort((a, b) => {
    if (a.order === b.order) {
      return a.title.localeCompare(b.title);
    }
    return a.order - b.order;
  });
}

export function getThesisEntry(slug: string | undefined): ThesisEntry | undefined {
  if (!slug) return undefined;
  return thesisEntries.find((entry) => entry.slug === slug);
}
