(function () {
  const attr = 'data-plot-json';
  const nodes = document.querySelectorAll(`[${attr}]`);
  if (!nodes.length || typeof Plotly === 'undefined') return;

  nodes.forEach((node) => {
    const path = node.getAttribute(attr);
    if (!path) return;
    fetch(path)
      .then((res) => res.json())
      .then((spec) => {
        const data = spec.data || [];
        const layout = Object.assign({}, spec.layout || {});
        const config = Object.assign({ responsive: true, displaylogo: false }, spec.config || {});
        Plotly.newPlot(node, data, layout, config);
      })
      .catch((err) => {
        console.error('Plotly hydrate failed for', path, err);
      });
  });
})();
