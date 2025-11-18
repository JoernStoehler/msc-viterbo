import { useEffect, useRef } from 'react';
import type { PlotlySpec } from '../lib/figures';

const loadPlotly = (() => {
  let cache: Promise<typeof import('plotly.js-dist-min')> | null = null;
  return () => {
    if (!cache) {
      cache = import('plotly.js-dist-min');
    }
    return cache;
  };
})();

interface PlotIslandProps {
  spec: PlotlySpec;
  title?: string;
}

export default function PlotIsland({ spec, title }: PlotIslandProps) {
  const ref = useRef<HTMLDivElement | null>(null);

  useEffect(() => {
    let disposed = false;

    loadPlotly()
      .then(async (Plotly) => {
        if (disposed || !ref.current) {
          return;
        }
        const data = JSON.parse(JSON.stringify(spec.data ?? []));
        const layout = {
          ...(spec.layout ?? {}),
          title: (spec.layout ?? {}).title ?? title,
        } as Record<string, unknown>;
        const config = {
          responsive: true,
          displaylogo: false,
          ...(spec.config ?? {}),
        } as Record<string, unknown>;
        await Plotly.newPlot(ref.current, data, layout, config);
      })
      .catch((error) => {
        console.error('Failed to load Plotly', error);
      });

    return () => {
      disposed = true;
      loadPlotly()
        .then((Plotly) => {
          if (ref.current) {
            Plotly.purge(ref.current);
          }
        })
        .catch(() => undefined);
    };
  }, [spec, title]);

  return <div ref={ref} style={{ width: '100%', minHeight: '320px' }} />;
}
