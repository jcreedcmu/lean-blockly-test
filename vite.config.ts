import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react-swc'
import svgr from "vite-plugin-svgr"


// https://vitejs.dev/config/
export default defineConfig({
  optimizeDeps: {
    exclude: ['Projects']
  },
  build: {
    // Relative to the root
    // Note: This has to match the path in `server/index.mjs` and in `tsconfig.json`
    outDir: 'client/dist',
  },
  plugins: [
    react(),
    svgr({
      // svgr options: https://react-svgr.com/docs/options/
      svgrOptions: { exportType: "default", ref: true, svgo: false, titleProp: true },
       include: "**/*.svg",
      }),
  ],
  publicDir: "client/public/",
  base: "/", // setting this to `/leanweb/` means the server is now accessible at `localhost:3000/leanweb`
  server: {
    port: 3000,
    proxy: {
      '/websocket': {
        target: 'ws://localhost:8080',
        ws: true
      },
      '/api': {
        target: 'http://localhost:8080',
      },
    }
  },
})
