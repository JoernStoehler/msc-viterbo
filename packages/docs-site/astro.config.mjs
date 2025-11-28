import { defineConfig } from 'astro/config';
import mdx from '@astrojs/mdx';
import react from '@astrojs/react';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const docsSiteRoot = fileURLToPath(new URL('.', import.meta.url));
const thesisSrc = path.join(docsSiteRoot, '..', 'thesis', 'src');

export default defineConfig({
  integrations: [
    mdx({
      remarkPlugins: [remarkMath],
      rehypePlugins: [rehypeKatex],
    }),
    react(),
  ],
  vite: {
    server: {
      fs: {
        allow: [docsSiteRoot, thesisSrc],
      },
    },
    resolve: {
      alias: {
        '#thesis': thesisSrc,
      },
    },
  },
  markdown: {
    shikiConfig: {
      theme: 'github-dark-default',
    },
  },
});
