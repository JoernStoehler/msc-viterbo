import type { FigureMeta } from './thesis';

export interface PlotlySpec {
  data: unknown[];
  layout?: Record<string, unknown>;
  config?: Record<string, unknown>;
}

const thesisAssetsBase = new URL('../../../thesis/src/', import.meta.url);

const figureSpecModules = import.meta.glob<PlotlySpec>(
  '../../../thesis/src/assets/figures/**/*.json',
  {
    eager: true,
    import: 'default',
  }
);

const figureSpecs = new Map<string, PlotlySpec>();

for (const [absolutePath, module] of Object.entries(figureSpecModules)) {
  const relative = normalizeRelativePath(absolutePath);
  figureSpecs.set(relative, module as PlotlySpec);
}

function normalizeRelativePath(filePath: string): string {
  const normalized = filePath.replace(/\\/g, '/');
  const marker = '/packages/thesis/src/';
  const idx = normalized.indexOf(marker);
  const tail = idx >= 0 ? normalized.slice(idx + marker.length) : normalized;
  return tail.replace(/^\.\//, '');
}

function normalizeRequestPath(relativePath: string): string {
  return relativePath.replace(/^\.\//, '').replace(/\\/g, '/');
}

export function getFigureSpec(relativePath: string | undefined): PlotlySpec | undefined {
  if (!relativePath) return undefined;
  const normalized = normalizeRequestPath(relativePath);
  return figureSpecs.get(normalized);
}

export function getStaticFigureUrl(figure: FigureMeta): URL {
  const normalized = normalizeRequestPath(figure.assets.static);
  return new URL(normalized, thesisAssetsBase);
}
