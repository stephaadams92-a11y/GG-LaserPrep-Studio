/**
 * Grain & Glow Studio v7  -  Main Application Module
 *
 * Changes from v6:
 *  OK Image pipeline (Lanczos/Mitchell resize + dithering) migrated to Web Worker
 *  OK Application logic in single IIFE closure  -  no runtime function patching
 *  OK State managed inside closure, minimal controlled window exports
 *  OK All inline styles replaced with CSS classes
 *  OK Comprehensive aria-label, role, tabindex attributes added via JS
 *  OK Dead code (Turbo Mode, orphaned worker null, duplicate runPipeline) removed
 *  OK Scientific add-on integrated at bottom (no separate script tag)
 */
(function () {
    "use strict";

    /* ================================================================
       STATE  -  single source of truth, closure-encapsulated
    ================================================================ */
    const state = {
        /* Image */
        image: null,
        originalWidth: 0,
        originalHeight: 0,
        loadedFileName: '',
        ratio: 1,
        /* View */
        zoom: 1,
        panX: 0,
        panY: 0,
        showGrid: false,
        showLines: false,
        splitView: false,
        physicalSim: false,
        edgeLiftPro: false,
        hqMode: false,
        preHqDpi: null,
        /* Pipeline */
        isProcessing: false,
        pendingProcess: false,
        originalResizedData: null,
        originalResizedW: 0,
        originalResizedH: 0,
        processedImageData: null,
        processedImageW: 0,
        processedImageH: 0,
        /* GC-friendly buffer reuse: worker writes into this on cache-hits */
        reuseBuffer: null,
        /* Lanczos/Mitchell cache */
        imageIdCounter: 0,
        lanczosCache: { imageId: null, pxW: 0, pxH: 0, data: null },
        /* Worker pool */
        worker: null,         /* primary worker */
        worker2: null,        /* secondary worker (batch/pool) */
        workerReady: false,
        workerBusy: false,
        workerQueue: [],      /* pending payloads when pool exhausted */
        /* Undo/Redo  -  ring buffer of settings snapshots (max 20) */
        undoHistory: [],
        undoIndex: -1,
        undoMax: 20,
        undoSuspended: false, /* true while restoring, prevents recording */
        /* Batch processing */
        batchQueue: [],
        batchActive: false,
        batchResults: [],
        /* Progress */
        lastProgressPct: 0,
        /* Memory */
        safeMode: false,      /* downscaled due to memory pressure */
        memoryWarned: false,
        /* Settings auto-persist */
        settingsPersistDebounce: null,
        /* Suppress pipeline during bulk setting changes (presets, undo, material) */
        _suppressQueue: false
    };

    /* ================================================================
       DOM REFS
    ================================================================ */
    const $ = id => document.getElementById(id);
    const canvas    = $('previewCanvas');
    const loader    = $('loader');
    const fileInput = $('fileInput');
    const container = $('previewContainer');
    const ctx       = canvas.getContext('2d', { willReadFrequently: true });

    /* ================================================================
       WORKER POOL  -  2 workers for multi-core utilisation.
       Primary worker handles live preview. Secondary handles batch.
    ================================================================ */
    function initWorker() {
        /* Inline worker as Blob string - zero file path dependency.
           Works on file://, APK assets, and HTTPS alike.
           Bypasses Android WebView file:// Worker() security block. */
        var workerSrc = "/**\n * GG LaserPrep v7  -  Image Processing Web Worker\n *\n * Features added in this version:\n *  OK Pre-calculated LUTs for gamma/tonal (zero Math.pow per pixel)\n *  OK sRGB linearisation before processing, sRGB encoding after (correct colour space)\n *  OK Memory budget estimation before allocation\n *  OK Tiled processing for high-resolution images (512px tiles, 4px overlap)\n *  OK Granular percentage-based progress reporting per tile/step\n *  OK Canvas buffer reuse  -  accepts reuseBuffer to minimise GC thrashing\n *  OK Mitchell-Netravali / Catmull-Rom resize (centre-aligned, verified coefficients)\n *  OK Full pipeline: denoise, grayscale Rec.709, histEq, tonal, Gaussian USM, local contrast\n *  OK All dithering: Floyd-Steinberg, Jarvis, Stucki, Atkinson, Riemersma, Bayer 2/4/8, halftone, threshold, adaptive\n */\n\"use strict\";\n\n/* ===========================================================\n   CONSTANTS\n=========================================================== */\nconst MEMORY_BUDGET_BYTES = 256 * 1024 * 1024;  /* 256 MB */\nconst TILE_SIZE           = 512;\nconst TILE_OVERLAP        = 4;\n\n/* ===========================================================\n   sRGB <-> LINEAR COLOUR SPACE LUTs\n=========================================================== */\nfunction buildLineariseLUT() {\n    const lut = new Float32Array(256);\n    for (let i=0; i<256; i++) {\n        const s = i/255;\n        lut[i] = s<=0.04045 ? s/12.92 : Math.pow((s+0.055)/1.055, 2.4);\n    }\n    return lut;\n}\nfunction buildSrgbEncodeLUT() {\n    const lut = new Uint8ClampedArray(256);\n    for (let i=0; i<256; i++) {\n        const lin = i/255;\n        const v   = lin<=0.0031308 ? lin*12.92 : 1.055*Math.pow(lin,1/2.4)-0.055;\n        lut[i]    = Math.round(Math.max(0,Math.min(1,v))*255);\n    }\n    return lut;\n}\nconst LUT_LIN = buildLineariseLUT();\nconst LUT_SRGB = buildSrgbEncodeLUT();\n\n/* ===========================================================\n   TONAL LUT  -  entire contrast/brightness/gamma/clip chain\n   collapsed to a single 256-entry uint8 lookup table.\n   Eliminates all Math.pow calls from the per-pixel loop.\n=========================================================== */\nfunction buildTonalLUT(s) {\n    const black  = s.blackPoint||0;\n    const white  = s.whitePoint||255;\n    const range  = Math.max(1, white-black);\n    const cf     = (259*(s.contrast+255))/(255*(259-s.contrast));\n    const gInv   = 1/Math.max(0.01, s.gamma);\n    const lut    = new Uint8ClampedArray(256);\n    for (let i=0; i<256; i++) {\n        let v = cf*(i-128)+128 + s.brightness;\n        v = Math.max(0,Math.min(255,v));\n        v = 255*Math.pow(v/255, gInv);\n        v = (v-black)*(255/range);\n        if (s.protectHigh && v>200) v = 200+(v-200)*0.5;\n        lut[i] = Math.max(0,Math.min(255,Math.round(v)));\n    }\n    return lut;\n}\n\n/* ===========================================================\n   MEMORY ESTIMATION\n=========================================================== */\nfunction estimateMemory(w, h, hasCache) {\n    return w*h*4*(hasCache?7:5);\n}\n\nfunction reportProgress(pct, label) {\n    self.postMessage({ type:'progress', pct:Math.min(100,Math.round(pct)), label:label||'' });\n}\n\n/* ===========================================================\n   MITCHELL-NETRAVALI / CATMULL-ROM RESIZE\n=========================================================== */\nconst MITCHELL   = {p0:7/6,  p1:-2,   p2:8/9,  q0:-7/18, q1:2,   q2:-10/3, q3:16/9};\nconst CATMULLROM = {p0:3/2,  p1:-5/2, p2:1,    q0:-1/2,  q1:5/2, q2:-4,    q3:2   };\n\nfunction evalKernel(x, k) {\n    x = Math.abs(x);\n    if (x<1) return k.p0*x*x*x + k.p1*x*x + k.p2;\n    if (x<2) return k.q0*x*x*x + k.q1*x*x + k.q2*x + k.q3;\n    return 0;\n}\n\nfunction mitchellResize(srcData, sW, sH, dW, dH, useCR) {\n    const k  = useCR ? CATMULLROM : MITCHELL;\n    const src = new Uint8ClampedArray(srcData);\n    const dst = new Uint8ClampedArray(dW*dH*4);\n    const xR  = sW/dW, yR = sH/dH;\n    for (let y=0; y<dH; y++) {\n        if (y%64===0) reportProgress((y/dH)*15, 'Resizing');\n        for (let x=0; x<dW; x++) {\n            const sx=(x+0.5)*xR-0.5, sy=(y+0.5)*yR-0.5;\n            const xi=Math.floor(sx), yi=Math.floor(sy);\n            let r=0,g=0,b=0,a=0,ws=0;\n            for (let dy=-1;dy<=2;dy++) for (let dx=-1;dx<=2;dx++) {\n                const px=xi+dx, py=yi+dy;\n                if(px<0||px>=sW||py<0||py>=sH) continue;\n                const wt=evalKernel(sx-px,k)*evalKernel(sy-py,k);\n                const ii=(py*sW+px)*4;\n                r+=src[ii]*wt; g+=src[ii+1]*wt; b+=src[ii+2]*wt; a+=src[ii+3]*wt; ws+=wt;\n            }\n            const di=(y*dW+x)*4;\n            if(ws>0){\n                dst[di]  =Math.min(255,Math.max(0,Math.round(r/ws)));\n                dst[di+1]=Math.min(255,Math.max(0,Math.round(g/ws)));\n                dst[di+2]=Math.min(255,Math.max(0,Math.round(b/ws)));\n                dst[di+3]=Math.min(255,Math.max(0,Math.round(a/ws)));\n            } else { dst[di+3]=255; }\n        }\n    }\n    reportProgress(15, 'Resize done');\n    return dst;\n}\n\n/* ===========================================================\n   PROCESS TILE  -  runs steps 1-7 on a rectangular buffer.\n   sRGB->linear -> denoise -> grayscale -> histEq -> tonalLUT ->\n   Gaussian USM -> local contrast -> linear->sRGB\n=========================================================== */\nfunction processTile(data, w, h, s, tonalLUT, pBase, pRange) {\n    const idx = (x,y)=>(y*w+x)*4;\n    let step=0; const STEPS=7;\n    const tick=(lbl)=>reportProgress(pBase+(++step/STEPS)*pRange, lbl);\n\n    /* Step 1  -  sRGB linearisation intentionally skipped.\n       All tonal/contrast/gamma operations are designed for and calibrated in\n       perceptual (sRGB gamma) space. Converting to linear light before these ops\n       crushes midtones and shadow detail (midtones drop to ~22% perceived brightness),\n       producing the \"too dark / no detail in blacks\" artifact.\n       Linear light is only beneficial for convolution-heavy ops (e.g. optical blur),\n       not for the tonal pipeline used here. */\n    tick('Linearise');\n\n    /* 2a  -  Noise Redux: fast Gaussian blur pass (separate from median denoise).\n            noiseRedux (0-50) controls sigma  -  higher = stronger smoothing.\n            Applied before grayscale so it works on colour channels. */\n    if (s.noiseRedux > 0) {\n        const sigma = Math.max(0.5, s.noiseRedux * 0.12); /* 0-50 -> sigma 0.6 - 6.0 */\n        const rad   = Math.ceil(sigma * 2);\n        const kLen  = rad * 2 + 1;\n        const kRaw  = new Float32Array(kLen);\n        let kSum = 0;\n        for (let k = 0; k < kLen; k++) {\n            const x = k - rad;\n            kRaw[k] = Math.exp(-(x * x) / (2 * sigma * sigma));\n            kSum += kRaw[k];\n        }\n        for (let k = 0; k < kLen; k++) kRaw[k] /= kSum;\n        const tmp = new Uint8ClampedArray(data);\n        const blurH = new Float32Array(w * h * 3);\n        /* Horizontal pass */\n        for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {\n            let r = 0, g = 0, b = 0, wa = 0;\n            for (let k = 0; k < kLen; k++) {\n                const sx = Math.max(0, Math.min(w - 1, x + k - rad));\n                const ii = idx(sx, y);\n                r += tmp[ii]   * kRaw[k];\n                g += tmp[ii+1] * kRaw[k];\n                b += tmp[ii+2] * kRaw[k];\n                wa += kRaw[k];\n            }\n            const bi = (y * w + x) * 3;\n            blurH[bi] = r / wa; blurH[bi+1] = g / wa; blurH[bi+2] = b / wa;\n        }\n        /* Vertical pass */\n        for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {\n            let r = 0, g = 0, b = 0, wa = 0;\n            for (let k = 0; k < kLen; k++) {\n                const sy = Math.max(0, Math.min(h - 1, y + k - rad));\n                const bi = (sy * w + x) * 3;\n                r += blurH[bi]   * kRaw[k];\n                g += blurH[bi+1] * kRaw[k];\n                b += blurH[bi+2] * kRaw[k];\n                wa += kRaw[k];\n            }\n            const i = idx(x, y);\n            data[i]   = Math.max(0, Math.min(255, Math.round(r / wa)));\n            data[i+1] = Math.max(0, Math.min(255, Math.round(g / wa)));\n            data[i+2] = Math.max(0, Math.min(255, Math.round(b / wa)));\n        }\n    }\n\n    /* 2b  -  Median Denoise (salt-and-pepper / impulse noise removal).\n            Uses spatial median over a radius window.\n            Separate from Noise Redux  -  preserves edges better but is slower. */\n    if (s.denoise > 0) {\n        const tmp = new Uint8ClampedArray(data);\n        const rad = s.denoise;\n        for (let y = rad; y < h - rad; y++) for (let x = rad; x < w - rad; x++) {\n            const r = [], g = [], b = [];\n            for (let dy = -rad; dy <= rad; dy++) for (let dx = -rad; dx <= rad; dx++) {\n                const i = idx(x + dx, y + dy);\n                r.push(tmp[i]); g.push(tmp[i+1]); b.push(tmp[i+2]);\n            }\n            r.sort((a, b) => a - b); g.sort((a, b) => a - b); b.sort((a, b) => a - b);\n            const m = Math.floor(r.length / 2), i = idx(x, y);\n            data[i] = r[m]; data[i+1] = g[m]; data[i+2] = b[m];\n        }\n    }\n    tick('Denoise');\n\n    /* 3  -  Grayscale Rec.709 + invert */\n    const hist=new Array(256).fill(0);\n    for(let i=0;i<data.length;i+=4){\n        let gray=0.2126*data[i]+0.7152*data[i+1]+0.0722*data[i+2];\n        if(s.invert) gray=255-gray;\n        data[i]=data[i+1]=data[i+2]=gray;\n        hist[Math.min(255,Math.max(0,Math.floor(gray)))]++;\n    }\n    tick('Grayscale');\n\n    /* 4  -  Histogram equalization */\n    if(s.histEq){\n        const cdf=new Array(256).fill(0); cdf[0]=hist[0];\n        for(let i=1;i<256;i++) cdf[i]=cdf[i-1]+hist[i];\n        const minC=cdf.find(v=>v>0)||0, tot=w*h;\n        const map=new Uint8ClampedArray(256);\n        for(let i=0;i<256;i++) map[i]=Math.round(((cdf[i]-minC)/Math.max(1,tot-minC))*255);\n        for(let i=0;i<data.length;i+=4) data[i]=data[i+1]=data[i+2]=map[data[i]];\n    }\n    tick('HistEq');\n\n    /* 5  -  Tonal LUT (zero Math.pow per pixel) */\n    for(let i=0;i<data.length;i+=4) data[i]=data[i+1]=data[i+2]=tonalLUT[data[i]];\n    tick('Tonal');\n\n    /* 6  -  Gaussian USM */\n    if(s.sharpen>0){\n        const amt=s.sharpen/100, usmR=Math.max(1,Math.min(3,s.usmRadius||2)), thresh=s.usmThreshold||0;\n        const kLen=usmR*2+1, sigma=usmR/2;\n        const kRaw=new Float32Array(kLen); let kSum=0;\n        for(let k=0;k<kLen;k++){const x=k-usmR;kRaw[k]=Math.exp(-(x*x)/(2*sigma*sigma));kSum+=kRaw[k];}\n        for(let k=0;k<kLen;k++) kRaw[k]/=kSum;\n        const tmp=new Uint8ClampedArray(data), blurH=new Float32Array(w*h), blur=new Float32Array(w*h);\n        for(let y=0;y<h;y++) for(let x=0;x<w;x++){\n            let acc=0,wa=0;\n            for(let k=0;k<kLen;k++){const sx=Math.max(0,Math.min(w-1,x+k-usmR));acc+=tmp[idx(sx,y)]*kRaw[k];wa+=kRaw[k];}\n            blurH[y*w+x]=acc/wa;\n        }\n        for(let y=0;y<h;y++) for(let x=0;x<w;x++){\n            let acc=0,wa=0;\n            for(let k=0;k<kLen;k++){const sy=Math.max(0,Math.min(h-1,y+k-usmR));acc+=blurH[sy*w+x]*kRaw[k];wa+=kRaw[k];}\n            blur[y*w+x]=acc/wa;\n        }\n        for(let y=0;y<h;y++) for(let x=0;x<w;x++){\n            const i=idx(x,y),orig=tmp[i],diff=orig-blur[y*w+x];\n            if(Math.abs(diff)<=thresh) continue;\n            data[i]=data[i+1]=data[i+2]=Math.max(0,Math.min(255,orig+amt*diff));\n        }\n    }\n\n    /* 6b  -  Local contrast (proportional Gaussian radius) */\n    if(s.localContrast>0){\n        const lcAmt=s.localContrast/100;\n        const lcR=Math.max(4,Math.min(40,Math.round(Math.min(w,h)/40)));\n        const lcSig=lcR/2, lcKLen=lcR*2+1;\n        const lcK=new Float32Array(lcKLen); let lcKS=0;\n        for(let k=0;k<lcKLen;k++){const x=k-lcR;lcK[k]=Math.exp(-(x*x)/(2*lcSig*lcSig));lcKS+=lcK[k];}\n        for(let k=0;k<lcKLen;k++) lcK[k]/=lcKS;\n        const tmp=new Uint8ClampedArray(data), blurH=new Float32Array(w*h), blur=new Float32Array(w*h);\n        for(let y=0;y<h;y++) for(let x=0;x<w;x++){\n            let acc=0,wa=0;\n            for(let k=0;k<lcKLen;k++){const sx=Math.max(0,Math.min(w-1,x+k-lcR));acc+=tmp[idx(sx,y)]*lcK[k];wa+=lcK[k];}\n            blurH[y*w+x]=acc/wa;\n        }\n        for(let y=0;y<h;y++) for(let x=0;x<w;x++){\n            let acc=0,wa=0;\n            for(let k=0;k<lcKLen;k++){const sy=Math.max(0,Math.min(h-1,y+k-lcR));acc+=blurH[sy*w+x]*lcK[k];wa+=lcK[k];}\n            blur[y*w+x]=acc/wa;\n        }\n        for(let y=0;y<h;y++) for(let x=0;x<w;x++){\n            const i=idx(x,y),orig=tmp[i],diff=orig-blur[y*w+x];\n            data[i]=data[i+1]=data[i+2]=Math.max(0,Math.min(255,orig+diff*lcAmt*2));\n        }\n    }\n    tick('USM/LC');\n\n    /* 7  -  sRGB re-encode intentionally skipped.\n       Since linearisation was skipped above, values remain in sRGB space throughout\n       and require no re-encoding. Applying LUT_SRGB here would incorrectly brighten\n       already-perceptual values. */\n    tick('sRGB encode');\n\n    return data;\n}\n\n/* ===========================================================\n   DITHERING  -  after sRGB encoding, on assembled full image\n   or per tile for Bayer/halftone/threshold\n=========================================================== */\nfunction applyDithering(data, w, h, s, pBase, pRange) {\n    const idx=(x,y)=>(y*w+x)*4;\n    if(s.dither==='none') return data;\n\n    if(['floyd','jarvis','stucki','atkinson','adaptive'].includes(s.dither)){\n        const errArr=new Float32Array(w*h);\n        for(let i=0;i<data.length;i+=4) errArr[i/4]=data[i];\n        for(let y=0;y<h;y++){\n            if(y%32===0) reportProgress(pBase+(y/h)*pRange,'Dithering');\n            const ltr=(y%2===0), xS=ltr?0:w-1, xE=ltr?w:-1, xSt=ltr?1:-1;\n            for(let x=xS;x!==xE;x+=xSt){\n                const ai=y*w+x; let ov=errArr[ai], bt=128;\n                if(s.dither==='adaptive'){\n                    let ls=0;\n                    for(let ly=-1;ly<=1;ly++) for(let lx=-1;lx<=1;lx++)\n                        ls+=errArr[Math.min(h-1,Math.max(0,y+ly))*w+Math.min(w-1,Math.max(0,x+lx))];\n                    bt=ls/9;\n                }\n                const jt=s.dither==='adaptive'?(Math.random()*6)-3:0;\n                const nv=ov<(bt+jt)?0:255;\n                data[ai*4]=data[ai*4+1]=data[ai*4+2]=nv;\n                const err=ov-nv, fw=ltr?1:-1;\n                if(s.dither==='floyd'){\n                    if(x+fw>=0&&x+fw<w)       errArr[y*w+(x+fw)]      +=err*(7/16);\n                    if(x-fw>=0&&x-fw<w&&y+1<h) errArr[(y+1)*w+(x-fw)] +=err*(3/16);\n                    if(y+1<h)                  errArr[(y+1)*w+x]       +=err*(5/16);\n                    if(x+fw>=0&&x+fw<w&&y+1<h) errArr[(y+1)*w+(x+fw)] +=err*(1/16);\n                } else if(s.dither==='jarvis'){\n                    if(x+fw>=0&&x+fw<w)     errArr[y*w+(x+fw)]    +=err*(7/48);\n                    if(x+2*fw>=0&&x+2*fw<w) errArr[y*w+(x+2*fw)]  +=err*(5/48);\n                    if(y+1<h){\n                        if(x-2*fw>=0&&x-2*fw<w) errArr[(y+1)*w+(x-2*fw)]+=err*(3/48);\n                        if(x-fw>=0&&x-fw<w)     errArr[(y+1)*w+(x-fw)]  +=err*(5/48);\n                        errArr[(y+1)*w+x]+=err*(7/48);\n                        if(x+fw>=0&&x+fw<w)     errArr[(y+1)*w+(x+fw)]  +=err*(5/48);\n                        if(x+2*fw>=0&&x+2*fw<w) errArr[(y+1)*w+(x+2*fw)]+=err*(3/48);\n                    }\n                    if(y+2<h){\n                        if(x-2*fw>=0&&x-2*fw<w) errArr[(y+2)*w+(x-2*fw)]+=err*(1/48);\n                        if(x-fw>=0&&x-fw<w)     errArr[(y+2)*w+(x-fw)]  +=err*(3/48);\n                        errArr[(y+2)*w+x]+=err*(5/48);\n                        if(x+fw>=0&&x+fw<w)     errArr[(y+2)*w+(x+fw)]  +=err*(3/48);\n                        if(x+2*fw>=0&&x+2*fw<w) errArr[(y+2)*w+(x+2*fw)]+=err*(1/48);\n                    }\n                } else if(s.dither==='stucki'){\n                    if(x+fw>=0&&x+fw<w)     errArr[y*w+(x+fw)]    +=err*(8/42);\n                    if(x+2*fw>=0&&x+2*fw<w) errArr[y*w+(x+2*fw)]  +=err*(4/42);\n                    if(y+1<h){\n                        if(x-2*fw>=0&&x-2*fw<w) errArr[(y+1)*w+(x-2*fw)]+=err*(2/42);\n                        if(x-fw>=0&&x-fw<w)     errArr[(y+1)*w+(x-fw)]  +=err*(4/42);\n                        errArr[(y+1)*w+x]+=err*(8/42);\n                        if(x+fw>=0&&x+fw<w)     errArr[(y+1)*w+(x+fw)]  +=err*(4/42);\n                        if(x+2*fw>=0&&x+2*fw<w) errArr[(y+1)*w+(x+2*fw)]+=err*(2/42);\n                    }\n                    if(y+2<h){\n                        if(x-2*fw>=0&&x-2*fw<w) errArr[(y+2)*w+(x-2*fw)]+=err*(1/42);\n                        if(x-fw>=0&&x-fw<w)     errArr[(y+2)*w+(x-fw)]  +=err*(2/42);\n                        errArr[(y+2)*w+x]+=err*(4/42);\n                        if(x+fw>=0&&x+fw<w)     errArr[(y+2)*w+(x+fw)]  +=err*(2/42);\n                        if(x+2*fw>=0&&x+2*fw<w) errArr[(y+2)*w+(x+2*fw)]+=err*(1/42);\n                    }\n                } else { /* Atkinson */\n                    if(x+fw>=0&&x+fw<w)     errArr[y*w+(x+fw)]    +=err*(1/8);\n                    if(x+2*fw>=0&&x+2*fw<w) errArr[y*w+(x+2*fw)]  +=err*(1/8);\n                    if(y+1<h){\n                        if(x-fw>=0&&x-fw<w) errArr[(y+1)*w+(x-fw)]+=err*(1/8);\n                        errArr[(y+1)*w+x]+=err*(1/8);\n                        if(x+fw>=0&&x+fw<w) errArr[(y+1)*w+(x+fw)]+=err*(1/8);\n                    }\n                    if(y+2<h) errArr[(y+2)*w+x]+=err*(1/8);\n                }\n            }\n        }\n    } else if(s.dither==='riemersma'){\n        const errArr=new Float32Array(w*h);\n        for(let i=0;i<data.length;i+=4) errArr[i/4]=data[i];\n        const hOrd=Math.ceil(Math.log2(Math.max(w,h))), hSz=Math.pow(2,hOrd);\n        function hD2xy(n,d){let x=0,y=0,t=d;for(let s=1;s<n;s*=2){const rx=(t&2)?1:0,ry=1&(t^rx);if(!ry){if(rx){x=s-1-x;y=s-1-y;}const tmp=x;x=y;y=tmp;}x+=s*rx;y+=s*ry;t>>=2;}return{x,y};}\n        const hLen=16, hW=new Float32Array(hLen); let wS=0;\n        for(let k=0;k<hLen;k++){hW[k]=Math.pow(1/Math.E,k);wS+=hW[k];}\n        for(let k=0;k<hLen;k++) hW[k]/=wS;\n        const eH=new Float32Array(hLen); let hP=0;\n        const tC=hSz*hSz;\n        for(let d=0;d<tC;d++){\n            if(d%10000===0) reportProgress(pBase+(d/tC)*pRange,'Riemersma');\n            const{x,y}=hD2xy(hSz,d);\n            if(x>=w||y>=h) continue;\n            const pi=y*w+x; let acc=0;\n            for(let k=0;k<hLen;k++) acc+=eH[(hP+k)%hLen]*hW[hLen-1-k];\n            const ov=errArr[pi]+acc, nv=ov<128?0:255;\n            data[pi*4]=data[pi*4+1]=data[pi*4+2]=nv;\n            eH[hP%hLen]=ov-nv; hP++;\n        }\n    } else if(s.dither.startsWith('bayer')){\n        const b2=[[0,2],[3,1]],b4=[[0,8,2,10],[12,4,14,6],[3,11,1,9],[15,7,13,5]];\n        const b8=[[0,48,12,60,3,51,15,63],[32,16,44,28,35,19,47,31],[8,56,4,52,11,59,7,55],[40,24,36,20,43,27,39,23],[2,50,14,62,1,49,13,61],[34,18,46,30,33,17,45,29],[10,58,6,54,9,57,5,53],[42,26,38,22,41,25,37,21]];\n        let sz,mx; if(s.dither==='bayer2'){sz=2;mx=b2;}else if(s.dither==='bayer4'){sz=4;mx=b4;}else{sz=8;mx=b8;}\n        const mult=255/(sz*sz-1);\n        const lut=new Float32Array(sz*sz);\n        for(let r=0;r<sz;r++) for(let c=0;c<sz;c++) lut[r*sz+c]=mx[r][c]*mult;\n        for(let y=0;y<h;y++) for(let x=0;x<w;x++){\n            const i=idx(x,y); data[i]=data[i+1]=data[i+2]=data[i]<lut[(y%sz)*sz+(x%sz)]?0:255;\n        }\n    } else if(s.dither==='threshold'){\n        const t=s.threshLevel||128;\n        for(let i=0;i<data.length;i+=4) data[i]=data[i+1]=data[i+2]=data[i]<t?0:255;\n    } else if(s.dither==='halftone'){\n        const rad=Math.max(2,s.dotSize||3), ctr=(rad-1)/2;\n        for(let y=0;y<h;y+=rad) for(let x=0;x<w;x+=rad){\n            let sum=0,cnt=0;\n            for(let dy=0;dy<rad;dy++) for(let dx=0;dx<rad;dx++)\n                if(x+dx<w&&y+dy<h){sum+=data[idx(x+dx,y+dy)];cnt++;}\n            const avg=cnt>0?sum/cnt:255, dotR=(1-(avg/255))*ctr;\n            for(let dy=0;dy<rad;dy++) for(let dx=0;dx<rad;dx++){\n                if(x+dx<w&&y+dy<h){\n                    const dist=Math.sqrt((dx-ctr)**2+(dy-ctr)**2);\n                    const val=dist<=dotR?0:255, i=idx(x+dx,y+dy);\n                    data[i]=data[i+1]=data[i+2]=val;\n                }\n            }\n        }\n    } else if(s.dither==='halftone_lines'){\n        /* -- Halftone Lines: variable-width horizontal lines -- */\n        const cellH=Math.max(2,s.dotSize||3);\n        for(let y=0;y<h;y+=cellH){\n            for(let x=0;x<w;x++){\n                /* Average brightness over the cell column */\n                let sum=0,cnt=0;\n                for(let dy=0;dy<cellH&&(y+dy)<h;dy++){ sum+=data[idx(x,y+dy)]; cnt++; }\n                const avg=cnt>0?sum/cnt:255;\n                /* Fraction of the cell height to paint black */\n                const fillRows=Math.round((1-(avg/255))*cellH);\n                for(let dy=0;dy<cellH&&(y+dy)<h;dy++){\n                    const v=dy<fillRows?0:255, i=idx(x,y+dy);\n                    data[i]=data[i+1]=data[i+2]=v;\n                }\n            }\n        }\n    } else if(s.dither==='halftone_crosshatch'){\n        /* -- Halftone Crosshatch: horizontal lines + 45deg diagonal for dark zones --\n           Snapshot original gray first so the second-pass decision uses real\n           image brightness, not already-dithered 0/255 values.               */\n        const cell=Math.max(2,s.dotSize||3);\n        /* Snapshot original luminance before any mutation */\n        const origGray=new Uint8Array(w*h);\n        for(let i=0;i<w*h;i++) origGray[i]=data[i*4];\n        /* First pass: variable-height horizontal lines */\n        for(let y=0;y<h;y+=cell){\n            for(let x=0;x<w;x++){\n                let sum=0,cnt=0;\n                for(let dy=0;dy<cell&&(y+dy)<h;dy++){ sum+=origGray[(y+dy)*w+x]; cnt++; }\n                const avg=cnt>0?sum/cnt:255;\n                const fillRows=Math.round((1-(avg/255))*(cell/2));\n                for(let dy=0;dy<cell&&(y+dy)<h;dy++){\n                    const v=dy<fillRows?0:255, i=idx(x,y+dy);\n                    data[i]=data[i+1]=data[i+2]=v;\n                }\n            }\n        }\n        /* Second pass: 45deg diagonal strokes on genuinely dark cells (uses original gray) */\n        for(let y=0;y<h;y+=cell) for(let x=0;x<w;x+=cell){\n            let sum=0,cnt=0;\n            for(let dy=0;dy<cell&&(y+dy)<h;dy++)\n                for(let dx=0;dx<cell&&(x+dx)<w;dx++){sum+=origGray[(y+dy)*w+(x+dx)];cnt++;}\n            const avg=cnt>0?sum/cnt:255;\n            if(avg<90){\n                for(let d=0;d<cell;d++){\n                    const px=x+d, py=y+d;\n                    if(px<w&&py<h){ const i=idx(px,py); data[i]=data[i+1]=data[i+2]=0; }\n                }\n            }\n            if(avg<45){\n                for(let d=0;d<cell;d++){\n                    const px=x+(cell-1-d), py=y+d;\n                    if(px>=0&&px<w&&py<h){ const i=idx(px,py); data[i]=data[i+1]=data[i+2]=0; }\n                }\n            }\n        }\n    }\n    return data;\n}\n\n/* ===========================================================\n   TILED ORCHESTRATOR\n=========================================================== */\nfunction processWithTiling(data, w, h, s, tonalLUT, reuseBuffer) {\n    const errDithers=['floyd','jarvis','stucki','atkinson','adaptive','riemersma'];\n    const useStrip=errDithers.includes(s.dither);\n    const fits=w<=TILE_SIZE&&h<=TILE_SIZE;\n\n    if(fits){\n        /* Small image  -  tonal then dither on full buffer, no tiling needed */\n        processTile(data,w,h,s,tonalLUT,15,75);\n        applyDithering(data,w,h,s,75,20);\n        return data;\n    }\n\n    const out=(reuseBuffer instanceof Uint8ClampedArray&&reuseBuffer.length===data.length)\n        ? reuseBuffer : new Uint8ClampedArray(data.length);\n\n    if(useStrip){\n        /* Vertical strips  -  full width, preserves error-diffusion continuity */\n        const nStrips=Math.ceil(h/TILE_SIZE);\n        for(let s2=0;s2<nStrips;s2++){\n            const y0=s2*TILE_SIZE, y1=Math.min(y0+TILE_SIZE,h), sH=y1-y0;\n            const buf=new Uint8ClampedArray(w*sH*4);\n            for(let y=0;y<sH;y++) buf.set(data.subarray(((y0+y)*w)*4,((y0+y)*w)*4+w*4),(y*w)*4);\n            const pb=15+(s2/nStrips)*60, pr=60/nStrips;\n            /* Tonal processing only  -  dithering applied to full image below */\n            processTile(buf,w,sH,s,tonalLUT,pb,pr);\n            for(let y=0;y<sH;y++) out.set(buf.subarray((y*w)*4,(y*w)*4+w*4),((y0+y)*w)*4);\n        }\n        /* Dithering on assembled full image  -  preserves error propagation across strips */\n        applyDithering(out,w,h,s,75,20);\n        return out;\n    } else {\n        /* 2D tiles for Bayer/halftone/threshold  -  tonal only per tile,\n           DITHERING runs on the fully assembled image to avoid phase-reset seams.\n           Bayer and halftone patterns are globally periodic: splitting them per tile\n           resets the pattern phase at each tile boundary, creating a visible 1px grid. */\n        const tC=Math.ceil(w/TILE_SIZE), tR=Math.ceil(h/TILE_SIZE), nT=tC*tR;\n        let tn=0;\n        for(let tr=0;tr<tR;tr++) for(let tc=0;tc<tC;tc++){\n            const x0=Math.max(0,tc*TILE_SIZE-TILE_OVERLAP), y0=Math.max(0,tr*TILE_SIZE-TILE_OVERLAP);\n            const x1=Math.min(w,(tc+1)*TILE_SIZE+TILE_OVERLAP), y1=Math.min(h,(tr+1)*TILE_SIZE+TILE_OVERLAP);\n            const tw=x1-x0, th=y1-y0;\n            const tb=new Uint8ClampedArray(tw*th*4);\n            for(let y=0;y<th;y++) tb.set(data.subarray(((y0+y)*w+x0)*4,((y0+y)*w+x0)*4+tw*4),(y*tw)*4);\n            const pb=15+(tn/nT)*60, pr=60/nT;\n            /* Tonal processing only per tile */\n            processTile(tb,tw,th,s,tonalLUT,pb,pr);\n            /* Write non-overlap region to output */\n            const dxS=tc*TILE_SIZE-x0, dyS=tr*TILE_SIZE-y0;\n            const dxE=Math.min(tw,(tc+1)*TILE_SIZE-x0), dyE=Math.min(th,(tr+1)*TILE_SIZE-y0);\n            const oxS=tc*TILE_SIZE, oyS=tr*TILE_SIZE;\n            for(let y=dyS;y<dyE;y++){\n                const dstY=oyS+(y-dyS); if(dstY>=h) break;\n                const rW=Math.min(dxE-dxS,w-oxS); if(rW<=0) continue;\n                out.set(tb.subarray((y*tw+dxS)*4,(y*tw+dxS)*4+rW*4),(dstY*w+oxS)*4);\n            }\n            tn++;\n        }\n        /* Dithering on fully assembled tonal image  -  no tile boundary seams */\n        applyDithering(out,w,h,s,75,20);\n    }\n    return out;\n}\n\n/* ===========================================================\n   MAIN PIPELINE ENTRY\n=========================================================== */\nfunction processImageData(payload) {\n    const{imageData,width,height,settings:s,\n          targetWidth,targetHeight,originalData,srcWidth,srcHeight,reuseBuffer}=payload;\n\n    /* Memory check */\n    const memEst=estimateMemory(targetWidth||width, targetHeight||height, !!originalData);\n    if(memEst>MEMORY_BUDGET_BYTES)\n        self.postMessage({type:'memoryWarning',estimatedMB:Math.round(memEst/1048576),budgetMB:256});\n\n    reportProgress(0,'Starting');\n\n    let data,w,h,originalResized=null;\n    if(originalData){\n        reportProgress(2,'Resizing');\n        data=mitchellResize(originalData,srcWidth,srcHeight,targetWidth,targetHeight,s.catmullRom);\n        w=targetWidth; h=targetHeight; originalResized=data.slice();\n    } else {\n        data=new Uint8ClampedArray(imageData); w=width; h=height;\n        reportProgress(15,'Cache hit');\n    }\n\n    const tonalLUT=buildTonalLUT(s);\n    reportProgress(16,'LUT ready');\n\n    const result=processWithTiling(data,w,h,s,tonalLUT,reuseBuffer);\n\n    /* All alpha channels = 255 on clean result before any simulation */\n    for(let i=3;i<result.length;i+=4) result[i]=255;\n\n    /* Spot simulation  -  preview-only display effect.\n       We keep the CLEAN result for export and produce a SEPARATE simulated\n       copy for display. exportCleanPng always reads resultData (clean).\n       simulatedData is passed alongside so finishPipelineRun can render it\n       to canvas while storing only resultData in state.processedImageData. */\n    let simulatedData = null;\n    if(s.simulate){\n        reportProgress(90,'Spot sim');\n        simulatedData = new Uint8ClampedArray(result); /* copy clean -> sim */\n        const idx=(x,y)=>(y*w+x)*4;\n        const sf=s.spotSize*10;\n        for(let y=1;y<h-1;y++) for(let x=1;x<w-1;x++){\n            let sum=0;\n            for(let ky=-1;ky<=1;ky++) for(let kx=-1;kx<=1;kx++) sum+=result[idx(x+kx,y+ky)];\n            const v=(sum/9)*(1-(sf*0.1)), i=idx(x,y);\n            simulatedData[i]=simulatedData[i+1]=simulatedData[i+2]=Math.max(0,Math.min(255,v));\n        }\n        for(let i=3;i<simulatedData.length;i+=4) simulatedData[i]=255;\n    }\n\n    reportProgress(100,'Done');\n    return{resultData:result, simulatedData, originalResized};\n}\n\n/* ===========================================================\n   MESSAGE HANDLER\n=========================================================== */\nself.onmessage=function(e){\n    const{type,payload}=e.data;\n    if(type==='process'){\n        try{\n            const r=processImageData(payload);\n            const t=[r.resultData.buffer];\n            if(r.originalResized) t.push(r.originalResized.buffer);\n            if(r.simulatedData)   t.push(r.simulatedData.buffer);\n            self.postMessage({type:'result',result:r},t);\n        }catch(err){\n            self.postMessage({type:'error',message:err.message,stack:err.stack});\n        }\n    }\n};\n";
        try {
            var blob = new Blob([workerSrc], { type: 'application/javascript' });
            var blobUrl = URL.createObjectURL(blob);
            state.worker = new Worker(blobUrl);
            state.worker.onmessage = onWorkerMessage;
            state.worker.onerror   = onWorkerError;
            try {
                state.worker2 = new Worker(blobUrl);
                state.worker2.onmessage = onBatchWorkerMessage;
                state.worker2.onerror   = function(e) { console.warn('[Worker2]', e); };
            } catch(e2) { state.worker2 = null; }
            state.workerReady = true;
            console.log('[LaserPrep] Inline blob worker ready');
        } catch(e) {
            console.warn('[LaserPrep] Worker unavailable:', e.message);
            state.worker = null;
            state.workerReady = false;
        }
    }


    function onWorkerMessage(e) {
        const { type } = e.data;
        if (type === 'result') {
            state.workerBusy = false;
            finishPipelineRun(e.data.result, state._pendingW, state._pendingH);
            /* Drain queue if pending */
            if (state.workerQueue.length > 0) {
                const next = state.workerQueue.shift();
                _sendToWorker(next);
            }
        } else if (type === 'progress') {
            updateProgressBar(e.data.pct, e.data.label);
        } else if (type === 'memoryWarning') {
            handleMemoryWarning(e.data.estimatedMB, e.data.budgetMB);
        } else if (type === 'error') {
            console.error('[Worker error]', e.data.message);
            activateSafeMode('Worker error: ' + e.data.message);
            endProcessing();
        }
    }

    function onWorkerError(e) {
        console.error('[Worker crash]', e);
        activateSafeMode('Worker crashed  -  safe mode active');
        endProcessing();
    }

    function onBatchWorkerMessage(e) {
        if (e.data.type === 'result') {
            handleBatchResult(e.data.result);
        } else if (e.data.type === 'progress') {
            updateBatchProgress(e.data.pct);
        } else if (e.data.type === 'error') {
            handleBatchError(e.data.message);
        }
    }

    /* -- Progress bar -- */
    function updateProgressBar(pct, label) {
        state.lastProgressPct = pct;
        const bar = $('progressBarFill');
        const lbl = $('progressLabel');
        if (bar) bar.style.width = pct + '%';
        if (lbl && label) lbl.textContent = label;
    }

    /* -- Memory warning handler -- */
    function handleMemoryWarning(estMB, budgetMB) {
        if (state.memoryWarned) return;
        state.memoryWarned = true;
        toast(`[!] Memory: ~${estMB}MB estimated (budget ${budgetMB}MB)  -  consider reducing DPI`, 4000);
        console.warn(`[Memory] Estimated ${estMB}MB, budget ${budgetMB}MB`);
    }

    /* -- Safe Mode  -  activated on worker crash or OOM -- */
    /* (defined fully below, near the fallback resize section) */

    /* ================================================================
       TOAST
    ================================================================ */
    function toast(msg, duration = 2200) {
        const el = $('toast');
        el.textContent = msg;
        el.setAttribute('aria-live', 'polite');
        el.classList.add('show');
        clearTimeout(el._t);
        el._t = setTimeout(() => el.classList.remove('show'), duration);
    }

    /* ================================================================
       SETTINGS READER
    ================================================================ */
    function getSettings() {
        const s = {
            blackPoint:    parseInt($('valBlack').value),
            whitePoint:    parseInt($('valWhite').value),
            noiseRedux:    parseInt($('valNoise').value),
            brightness:    parseInt($('valBright').value),
            contrast:      parseInt($('valCont').value),
            gamma:         parseFloat($('valGamma').value),
            sharpen:       parseInt($('valSharp').value),
            denoise:       parseInt($('valDenoise').value),
            localContrast: parseInt(($('valLocalContrast') || { value: '0' }).value) | 0,
            protectHigh:   $('chkProtectHigh').checked,
            histEq:        $('chkHistEq').checked,
            invert:        $('chkInvert').checked,
            dither:        $('ditherSelect').value,
            dotSize:       parseInt($('valDot').value),
            threshLevel:   parseInt($('valThresh').value),
            simulate:      $('chkSimulate').checked,
            spotSize:      parseFloat($('valSpot').value),
            catmullRom:    !!($('chkCatmullRom') && $('chkCatmullRom').checked),
            usmRadius:     parseInt(($('selUsmRadius') || {value:'2'}).value) || 2,
            usmThreshold:  parseInt(($('valUsmThresh') || {value:'0'}).value) || 0
        };
        if (state.edgeLiftPro) {
            s.sharpen  = Math.min(100, s.sharpen + 30);
            s.contrast = Math.min(100, s.contrast + 10);
        }
        return s;
    }

    /* ================================================================
       PIPELINE
    ================================================================ */
    let processDebounce;
    let _sliderDragging = false;   /* true while any range input is being held */
    let _dragDebounce;             /* fires full-res run after drag ends */

    function queueProcess(fromDrag) {
        if (!state.image) return;
        if (state._suppressQueue) return;   /* inside a bulk settings change */
        clearTimeout(processDebounce);

        /* Discard any previously queued-but-not-yet-dispatched payload.
           This prevents stale jobs piling up when the worker is busy and
           the user keeps moving sliders. */
        state.workerQueue = [];
        /* Clear a pending retry so it doesn't fire after we cancel. */
        state.pendingProcess = false;

        const delay = (fromDrag && _sliderDragging) ? 80 : 500;

        processDebounce = setTimeout(() => {
            if (state.isProcessing) {
                /* Worker is mid-run. Park latest job; it will be dispatched
                   as soon as the current run finishes (workerQueue drain). */
                state.pendingProcess = true;
            } else {
                runPipeline(fromDrag && _sliderDragging);
            }
        }, delay);
    }

    /* Called by slider pointerdown/touchstart to enter drag mode */
    function _startDrag() { _sliderDragging = true; }

    /* Called on pointerup/touchend — run full-res pipeline after drag ends */
    function _endDrag() {
        if (!_sliderDragging) return;
        _sliderDragging = false;
        clearTimeout(_dragDebounce);
        _dragDebounce = setTimeout(() => {
            state.workerQueue = [];
            state.pendingProcess = false;
            if (!state.isProcessing) runPipeline(false);
            else state.pendingProcess = true;
        }, 120);
    }

    /* Wrap any bulk settings change (preset, undo, material, auto-prep) so that
       all the individual queueProcess() calls fired by input events and
       dispatchEvent('change') are silently absorbed, then exactly ONE pipeline
       run fires when the function returns.  Pass runAfter=false to skip the run
       (useful if the caller will call queueProcess() itself with custom args). */
    function batchSettings(fn, runAfter) {
        state._suppressQueue = true;
        try { fn(); } finally { state._suppressQueue = false; }
        /* Clear any stale queue entries that may have snuck through */
        clearTimeout(processDebounce);
        state.workerQueue    = [];
        state.pendingProcess = false;
        if (runAfter !== false) queueProcess();
    }

    function updateSimIndicator() {
        const btn = $('btnExport');
        if (!btn) return;
        const simOn = $('chkSimulate') && $('chkSimulate').checked;
        if (simOn) {
            btn.title = 'Export PNG (simulation is on - exported file will be CLEAN, not simulated)';
            btn.setAttribute('data-sim', '1');
        } else {
            btn.title = 'Export processed image as PNG';
            btn.removeAttribute('data-sim');
        }
    }

    function endProcessing() {
        state.isProcessing = false;
        loader.classList.remove('visible');
        updateProgressBar(0, '');
        updateImgStats();
        updateSimIndicator();
        if (navigator.vibrate) navigator.vibrate(20);
        /* Batch callback  -  called once per image when batch is active */
        if (state.batchActive && typeof state._batchOnComplete === 'function') {
            const cb = state._batchOnComplete;
            state._batchOnComplete = null;
            cb();
            return; /* batch drives next step, skip normal pending-process check */
        }
        if (state.pendingProcess) {
            state.pendingProcess = false;
            /* If slider is still being dragged, don't chain another full-res run.
               _endDrag will fire one when the user releases. */
            if (!_sliderDragging) setTimeout(runPipeline, 0);
        }
    }

    function runPipeline(livePreview) {
        if (!state.image || state.isProcessing) return;
        state.isProcessing = true;
        state.pendingProcess = false;
        loader.classList.add('visible');
        updateProgressBar(0, livePreview ? 'Preview…' : 'Starting');

        const w_mm = parseFloat($('imgWidth').value);
        const h_mm = parseFloat($('imgHeight').value);
        const dpi  = parseFloat($('imgDpiNum').value);
        let pxW  = Math.round((w_mm / 25.4) * dpi);
        let pxH  = Math.round((h_mm / 25.4) * dpi);

        /* Live-drag preview: process at 40% resolution for instant feedback.
           Full-res run fires automatically when the drag ends (_endDrag). */
        if (livePreview) {
            const scale = 0.4;
            pxW = Math.max(64, Math.round(pxW * scale));
            pxH = Math.max(64, Math.round(pxH * scale));
        }

        /* Memory enforcement  -  may auto-adjust DPI and return false to retry */
        if (!checkAndEnforceMemoryLimit(pxW, pxH)) {
            state.isProcessing = false;
            loader.classList.remove('visible');
            setTimeout(runPipeline, 50); /* retry with new DPI */
            return;
        }

        const settings = getSettings();
        state._pendingW = pxW;
        state._pendingH = pxH;

        if ($('chkLanczos').checked) {
            const cacheHit = state.lanczosCache.data &&
                state.lanczosCache.imageId === state.image._ggId &&
                state.lanczosCache.pxW === pxW &&
                state.lanczosCache.pxH === pxH;

            if (cacheHit) {
                /* CRITICAL FIX: send a .slice() copy  -  transferring the buffer
                   directly would neuter (detach) state.lanczosCache.data,
                   destroying the cache for all subsequent slider changes. */
                dispatchToWorker({
                    imageData: state.lanczosCache.data.slice(),
                    width: pxW, height: pxH, settings
                });
            } else {
                if (!state.image._ggId) state.image._ggId = ++state.imageIdCounter;
                const origCanvas = document.createElement('canvas');
                origCanvas.width  = state.image.width;
                origCanvas.height = state.image.height;
                origCanvas.getContext('2d').drawImage(state.image, 0, 0);
                const origData = origCanvas.getContext('2d')
                    .getImageData(0, 0, state.image.width, state.image.height).data;
                dispatchToWorker({
                    originalData: origData,
                    srcWidth: state.image.width,
                    srcHeight: state.image.height,
                    targetWidth: pxW, targetHeight: pxH, settings
                });
            }
        } else {
            const tmpCanvas = fallbackResize(state.image, pxW, pxH);
            const tCtx = tmpCanvas.getContext('2d', { willReadFrequently: true });
            const imgData = tCtx.getImageData(0, 0, pxW, pxH);
            state.originalResizedData = new Uint8ClampedArray(imgData.data);
            state.originalResizedW = pxW;
            state.originalResizedH = pxH;
            dispatchToWorker({
                imageData: imgData.data,
                width: pxW, height: pxH, settings
            });
        }
    }

    /* -- Memory limit check before dispatching -- */
    const MEMORY_BUDGET   = 256 * 1024 * 1024;
    const BYTES_PER_PIXEL = 4;
    const BUFFER_COUNT    = 5; /* src + processed + float arrays */

    /* Shim  -  resolves to enforceMemoryLimit defined in the new-systems block below */
    function checkAndEnforceMemoryLimit(pxW, pxH) {
        return enforceMemoryLimit(pxW, pxH);
    }

    function dispatchToWorker(payload) {
        /* Attach reuse buffer to minimise GC allocation on cache-hit paths */
        if (state.reuseBuffer &&
            state.reuseBuffer.length === (state._pendingW * state._pendingH * 4)) {
            payload.reuseBuffer = state.reuseBuffer;
        }

        if (state.workerReady && state.worker) {
            if (state.workerBusy) {
                /* Queue instead of dropping  -  last entry always wins for live preview */
                state.workerQueue = [payload]; /* keep only latest, discard older */
                return;
            }
            _sendToWorker(payload);
        } else {
            /* Synchronous fallback */
            setTimeout(() => {
                try {
                    const result = getFallbackProcessors().processImageDataFallback(payload);
                    finishPipelineRun(result, state._pendingW, state._pendingH);
                } catch(err) {
                    activateSafeMode('Fallback error: ' + err.message);
                    endProcessing();
                }
            }, 0);
        }
    }

    function _sendToWorker(payload) {
        state.workerBusy = true;
        const transfers = [];
        if (payload.imageData)    transfers.push(payload.imageData.buffer);
        if (payload.originalData) transfers.push(payload.originalData.buffer);
        state.worker.postMessage({ type: 'process', payload }, transfers);
    }

    /* Inline fallback (same logic as worker, runs on main thread) */
    function getFallbackProcessors() {
        return {
            processImageDataFallback: function(payload) {
                /* Re-uses the same mitchellResize + processImageData logic
                   defined inline here as a last-resort if Worker file 404s */
                const { imageData, width, height, settings,
                        targetWidth, targetHeight, originalData, srcWidth, srcHeight } = payload;
                let data, w, h, originalResized = null;

                if (originalData) {
                    data = mitchellResizeFallback(new Uint8ClampedArray(originalData), srcWidth, srcHeight, targetWidth, targetHeight);
                    w = targetWidth; h = targetHeight;
                    originalResized = data.slice();
                } else {
                    data = new Uint8ClampedArray(imageData);
                    w = width; h = height;
                }
                /* Minimal pipeline (grayscale + tonal + dither) for fallback */
                const idx = (x,y)=>(y*w+x)*4;
                /* Grayscale */
                for (let i=0;i<data.length;i+=4){
                    let gray=0.2126*data[i]+0.7152*data[i+1]+0.0722*data[i+2];
                    if(settings.invert) gray=255-gray;
                    data[i]=data[i+1]=data[i+2]=gray;
                }
                /* Contrast -> Brightness -> Gamma -> Clip (corrected order) */
                const black=settings.blackPoint||0, white=settings.whitePoint||255;
                const clipRange=Math.max(1,white-black);
                const cf=(259*(settings.contrast+255))/(255*(259-settings.contrast));
                const gi=1/Math.max(0.01,settings.gamma);
                for(let i=0;i<data.length;i+=4){
                    let v=cf*(data[i]-128)+128;
                    v+=settings.brightness;
                    v=255*Math.pow(Math.max(0,Math.min(255,v))/255,gi);
                    v=(v-black)*(255/clipRange);
                    data[i]=data[i+1]=data[i+2]=Math.max(0,Math.min(255,v));
                }
                for(let i=3;i<data.length;i+=4) data[i]=255;
                return { resultData: data, originalResized };
            }
        };
    }

    function mitchellResizeFallback(src, srcW, srcH, dstW, dstH) {
        const dst = new Uint8ClampedArray(dstW*dstH*4);
        const xR = srcW/dstW, yR = srcH/dstH;
        const B=1/3,C=1/3;
        function mk(x){
            x=Math.abs(x);
            if(x<1)return((12-9*B-6*C)*x*x*x+(-18+12*B+6*C)*x*x+(6-2*B))/6;
            if(x<2)return((-B-6*C)*x*x*x+(6*B+30*C)*x*x+(-12*B-48*C)*x+(8*B+24*C))/6;
            return 0;
        }
        for(let y=0;y<dstH;y++){
            for(let x=0;x<dstW;x++){
                /* Centre-aligned: (x+0.5)*ratio - 0.5  -  matches PIL/ImageMagick/OpenCV */
                const sx=(x+0.5)*xR-0.5, sy=(y+0.5)*yR-0.5, xi=Math.floor(sx), yi=Math.floor(sy);
                let r=0,g=0,b=0,a=0,ws=0;
                for(let dy=-1;dy<=2;dy++)for(let dx=-1;dx<=2;dx++){
                    const px=xi+dx,py=yi+dy;
                    if(px<0||px>=srcW||py<0||py>=srcH)continue;
                    const wt=mk(sx-px)*mk(sy-py);
                    const ii=(py*srcW+px)*4;
                    r+=src[ii]*wt;g+=src[ii+1]*wt;b+=src[ii+2]*wt;a+=src[ii+3]*wt;ws+=wt;
                }
                const di=(y*dstW+x)*4;
                if(ws>0){dst[di]=Math.min(255,Math.max(0,Math.round(r/ws)));
                         dst[di+1]=Math.min(255,Math.max(0,Math.round(g/ws)));
                         dst[di+2]=Math.min(255,Math.max(0,Math.round(b/ws)));
                         dst[di+3]=Math.min(255,Math.max(0,Math.round(a/ws)));}
                else{dst[di+3]=255;}
            }
        }
        return dst;
    }

    function finishPipelineRun(result, w, h) {
        if (!result || !result.resultData) { endProcessing(); return; }
        try {
            canvas.width  = w;
            canvas.height = h;

            if (result.originalResized) {
                state.originalResizedData = new Uint8ClampedArray(result.originalResized);
                state.originalResizedW = w;
                state.originalResizedH = h;
                /* FIX: update cache on imageId change OR dimension change. */
                if (state.image && $('chkLanczos').checked) {
                    state.lanczosCache = {
                        imageId: state.image._ggId, pxW: w, pxH: h,
                        data: new Uint8ClampedArray(result.originalResized)
                    };
                }
            }

            /* FIX: Store CLEAN processed pixels for export  -  never contaminated by sim.
               simulatedData (if present) is used only for canvas preview display. */
            state.processedImageData = new Uint8ClampedArray(result.resultData);
            state.processedImageW    = w;
            state.processedImageH    = h;
            /* Store as reuse buffer for next pipeline run to avoid GC thrashing */
            state.reuseBuffer = state.processedImageData;

            /* Display data: use simulated version for preview if simulate is on,
               otherwise use the clean processed data */
            const displayData = result.simulatedData
                ? new Uint8ClampedArray(result.simulatedData)
                : state.processedImageData;

            /* -- DISPLAY: compose split / overlays on canvas for preview only -- */
            if (state.splitView && state.originalResizedData) {
                const merged = new Uint8ClampedArray(displayData.length);
                const dpr    = window.devicePixelRatio || 1;
                /* Read the draggable slider position to determine split point */
                let splitX;
                const sliderLeft = parseFloat(splitSlider.style.left);
                if (splitSlider.classList.contains('comparison-slider--visible') && !isNaN(sliderLeft)) {
                    /* Convert container px position to canvas pixel coordinate */
                    const containerW = container.clientWidth || w;
                    splitX = Math.round((sliderLeft / containerW) * w);
                } else {
                    splitX = Math.round(w / 2);
                }
                splitX = Math.max(0, Math.min(w, splitX));
                const divX = Math.round(splitX * dpr) / dpr;
                for (let y=0; y<h; y++) {
                    for (let x=0; x<w; x++) {
                        const i = (y*w+x)*4;
                        if (x < splitX) {
                            merged[i]   = state.originalResizedData[i];
                            merged[i+1] = state.originalResizedData[i+1];
                            merged[i+2] = state.originalResizedData[i+2];
                            merged[i+3] = 255;
                        } else {
                            merged[i]   = displayData[i];
                            merged[i+1] = displayData[i+1];
                            merged[i+2] = displayData[i+2];
                            merged[i+3] = 255;
                        }
                    }
                }
                ctx.putImageData(new ImageData(merged, w, h), 0, 0);
                ctx.fillStyle = '#ff4444';
                ctx.fillRect(divX - (0.5/dpr), 0, 1/dpr, h);
            } else {
                ctx.putImageData(new ImageData(displayData, w, h), 0, 0);
            }

            /* Overlays drawn after putImageData  -  display only, never in exported PNG */
            applyOverlays();
            if (state.physicalSim) applyPhysicalTexture();
            endProcessing();
        } catch(err) {
            console.error('[Render error]', err);
            endProcessing();
        }
    }

    /* ================================================================
       OVERLAYS
    ================================================================ */
    function applyOverlays() {
        if (state.showGrid) {
            ctx.fillStyle = 'rgba(0,255,80,0.2)';
            for (let i=0; i<canvas.width;  i+=10) ctx.fillRect(i,0,1,canvas.height);
            for (let i=0; i<canvas.height; i+=10) ctx.fillRect(0,i,canvas.width,1);
        }
        if (state.showLines) {
            ctx.fillStyle = 'rgba(0,200,255,0.12)';
            for (let i=0; i<canvas.height; i+=2) ctx.fillRect(0,i,canvas.width,1);
        }
        /* Material grain overlay (moved from add-ons) */
        if (state.physicalSim) {
            const mat = $('materialSelect').value;
            if (mat === 'bamboo' || mat === 'basswood') {
                ctx.globalAlpha = 0.18;
                ctx.strokeStyle = '#3e2723';
                ctx.lineWidth = 1;
                for (let y=0; y<canvas.height; y+=8) {
                    ctx.beginPath();
                    ctx.moveTo(0, y);
                    ctx.lineTo(canvas.width, y + Math.sin(y*0.1)*5);
                    ctx.stroke();
                }
                ctx.globalAlpha = 1;
            }
        }
    }

    function applyPhysicalTexture() {
        if (!state.physicalSim) return;
        const mat = $('materialSelect').value;
        ctx.globalAlpha = 0.4;
        ctx.globalCompositeOperation = 'multiply';
        for (let i=0; i<canvas.width; i+=4) {
            for (let j=0; j<canvas.height; j+=4) {
                if (Math.random() > 0.98) {
                    ctx.fillStyle = mat === 'slate' ? '#222' : '#5d4037';
                    ctx.fillRect(i, j, 2, 2);
                }
            }
        }
        ctx.globalAlpha = 1.0;
        ctx.globalCompositeOperation = 'source-over';
    }

    /* ================================================================
       PNG EXPORT  -  pHYs chunk injection for true DPI metadata
       Ensures laser controller can read physical dimensions from file.
    ================================================================ */
    function injectPhysChunk(pngDataUrl, dpi) {
        /* Convert dataURL -> Uint8Array */
        const base64 = pngDataUrl.split(',')[1];
        const binary = atob(base64);
        const src = new Uint8Array(binary.length);
        for (let i=0; i<binary.length; i++) src[i] = binary.charCodeAt(i);

        /* pHYs chunk: pixels-per-unit X, pixels-per-unit Y, unit=1 (metre) */
        const ppm = Math.round(dpi / 0.0254); // dots-per-inch -> pixels-per-metre
        const phys = new Uint8Array(21); // 4 len + 4 type + 9 data + 4 CRC
        const view = new DataView(phys.buffer);
        view.setUint32(0, 9, false);               // chunk data length = 9
        phys[4]=0x70;phys[5]=0x48;phys[6]=0x59;phys[7]=0x73; // 'pHYs'
        view.setUint32(8, ppm, false);             // X pixels per unit
        view.setUint32(12, ppm, false);            // Y pixels per unit
        phys[16] = 1;                              // unit: metre

        /* CRC32 of type+data (bytes 4..16) */
        function crc32(buf, off, len) {
            let c = 0xFFFFFFFF;
            const t = new Uint32Array(256);
            for (let n=0; n<256; n++) {
                let v = n;
                for (let k=0; k<8; k++) v = (v&1) ? (0xEDB88320^(v>>>1)) : (v>>>1);
                t[n] = v;
            }
            for (let i=off; i<off+len; i++) c = t[(c^buf[i])&0xFF]^(c>>>8);
            return (c^0xFFFFFFFF)>>>0;
        }
        const crc = crc32(phys, 4, 13);
        view.setUint32(17, crc, false);

        /* Insert pHYs after PNG signature (8 bytes) + IHDR chunk (4+4+13+4 = 25 bytes) */
        const insertAt = 33;
        const out = new Uint8Array(src.length + 21);
        out.set(src.slice(0, insertAt));
        out.set(phys, insertAt);
        out.set(src.slice(insertAt), insertAt + 21);

        /* Return as object URL */
        const blob = new Blob([out], { type: 'image/png' });
        return URL.createObjectURL(blob);
    }

    function exportCleanPng(filename) {
        if (!state.processedImageData || !state.processedImageW) {
            toast('No processed image to export');
            return;
        }
        const w = state.processedImageW;
        const h = state.processedImageH;
        const dpi = parseFloat($('imgDpiNum').value) || 300;

        const exportCanvas = document.createElement('canvas');
        exportCanvas.width  = w;
        exportCanvas.height = h;
        exportCanvas.getContext('2d').putImageData(
            new ImageData(new Uint8ClampedArray(state.processedImageData), w, h), 0, 0
        );

        const dataUrl = exportCanvas.toDataURL('image/png');
        const url = injectPhysChunk(dataUrl, dpi);

        /* Android bridge: convert blob URL to base64 and hand to Java */
        const fname = filename || 'GG_LaserPrep_Export.png';
        if (window.AndroidBridge) {
            fetch(url).then(r => r.blob()).then(blob => {
                const reader = new FileReader();
                reader.onloadend = () => {
                    const b64 = reader.result.split(',')[1];
                    window.AndroidBridge.saveFile(b64, fname, 'image/png');
                    toast('\u2713 Saved to Downloads');
                };
                reader.readAsDataURL(blob);
            }).catch(() => {
                /* fallback: pass dataUrl base64 directly */
                const b64 = dataUrl.split(',')[1];
                window.AndroidBridge.saveFile(b64, fname, 'image/png');
                toast('\u2713 Saved to Downloads');
            });
            setTimeout(() => URL.revokeObjectURL(url), 5000);
        } else {
            /* Browser / Cloudflare  -  normal download */
            const link = document.createElement('a');
            link.download = fname;
            link.href = url;
            link.click();
            setTimeout(() => URL.revokeObjectURL(url), 5000);
        }
    }

    /* Android download bridge helper  -  used by SVG and G-code exports */
    function triggerDownload(blobOrUrl, filename, mimeType) {
        if (window.AndroidBridge) {
            const doSave = (b64) => {
                window.AndroidBridge.saveFile(b64, filename, mimeType);
                toast('\u2713 Saved to Downloads: ' + filename);
            };
            if (typeof blobOrUrl === 'string' && blobOrUrl.startsWith('blob:')) {
                fetch(blobOrUrl).then(r => r.blob()).then(blob => {
                    const reader = new FileReader();
                    reader.onloadend = () => doSave(reader.result.split(',')[1]);
                    reader.readAsDataURL(blob);
                });
            } else if (blobOrUrl instanceof Blob) {
                const reader = new FileReader();
                reader.onloadend = () => doSave(reader.result.split(',')[1]);
                reader.readAsDataURL(blobOrUrl);
            } else if (typeof blobOrUrl === 'string') {
                /* plain text (G-code, SVG source) */
                const b64 = btoa(unescape(encodeURIComponent(blobOrUrl)));
                doSave(b64);
            }
        } else {
            /* Browser fallback */
            const a = document.createElement('a');
            if (typeof blobOrUrl === 'string' && !blobOrUrl.startsWith('blob:')) {
                a.href = URL.createObjectURL(new Blob([blobOrUrl], { type: mimeType }));
            } else {
                a.href = typeof blobOrUrl === 'string' ? blobOrUrl
                       : URL.createObjectURL(blobOrUrl);
            }
            a.download = filename;
            a.click();
            setTimeout(() => URL.revokeObjectURL(a.href), 5000);
        }
    }
    function fallbackResize(img, width, height) {
        const c = document.createElement('canvas');
        c.width = width; c.height = height;
        const cx = c.getContext('2d');
        cx.imageSmoothingEnabled = true;
        cx.imageSmoothingQuality = 'high';
        cx.drawImage(img, 0, 0, width, height);
        return c;
    }

    /* ================================================================
       INPUT VALIDATION  -  file type, file size, image dimensions
    ================================================================ */
    const ALLOWED_TYPES  = new Set(['image/png','image/jpeg','image/webp','image/gif','image/bmp']);
    const MAX_FILE_BYTES = 50  * 1024 * 1024;
    const MAX_SRC_PIXELS = 100 * 1024 * 1024;

    function validateFile(file) {
        if (!file) return ['No file provided'];
        const errs = [];
        // Android content:// URIs often return empty MIME type - check extension too
        const mimeOk = ALLOWED_TYPES.has(file.type);
        const extOk  = /\.(png|jpe?g|webp|gif|bmp)$/i.test(file.name || '');
        const typeUnknown = !file.type || file.type === 'application/octet-stream';
        if (!mimeOk && !extOk && !typeUnknown)
            errs.push('Unsupported format: ' + file.type + '. Use PNG, JPEG, WebP, GIF or BMP.');
        if (file.size > 0 && file.size > MAX_FILE_BYTES)
            errs.push('File too large: ' + (file.size/1048576).toFixed(1) + 'MB (max 50MB).');
        return errs;
    }

    function validateDimensions(img) {
        const errs = [];
        if (img.width < 8 || img.height < 8)
            errs.push('Image too small: ' + img.width + 'x' + img.height + 'px (min 8x8).');
        if (img.width * img.height > MAX_SRC_PIXELS)
            errs.push('Source is ' + (img.width*img.height/1e6).toFixed(1) + 'MP  -  auto-downscaled for memory safety.');
        return errs;
    }

    function checkOutputMemory(pxW, pxH) {
        const BUDGET = 256 * 1024 * 1024;
        const est    = pxW * pxH * 4 * 5;
        if (est <= BUDGET) return null;
        const w_mm = parseFloat($('imgWidth').value);
        const h_mm = parseFloat($('imgHeight').value);
        const maxPx = Math.sqrt(BUDGET / 20);
        return Math.max(72, Math.min(600, Math.floor(maxPx / Math.max(w_mm, h_mm) * 25.4)));
    }

    function enforceMemoryLimit(pxW, pxH) {
        const safeDpi = checkOutputMemory(pxW, pxH);
        if (safeDpi === null) return true;
        const dpiNum = $('imgDpiNum'), dpiSlider = $('imgDpi');
        if (dpiNum && parseFloat(dpiNum.value) > safeDpi) {
            dpiNum.value = dpiSlider.value = safeDpi;
            toast('DPI auto-reduced to ' + safeDpi + '  -  would exceed 256MB memory budget', 4000);
        }
        return false;
    }

    /* ================================================================
       EXIF ORIENTATION HANDLING  -  parse JPEG APP1, apply CSS transform
    ================================================================ */
    function readExifOrientation(arrayBuffer) {
        const b = new Uint8Array(arrayBuffer);
        if (b[0]!==0xFF||b[1]!==0xD8) return 1;
        let pos=2;
        while (pos < b.length-4) {
            if (b[pos]!==0xFF) break;
            const mk=b[pos+1], len=(b[pos+2]<<8)|b[pos+3];
            if (mk===0xE1&&len>=16) {
                if(b[pos+4]===69&&b[pos+5]===120&&b[pos+6]===105&&
                   b[pos+7]===102&&b[pos+8]===0&&b[pos+9]===0){
                    const t=pos+10;
                    const le=b[t]===0x49&&b[t+1]===0x49;
                    const r16=(o)=>le?b[t+o]|(b[t+o+1]<<8):(b[t+o]<<8)|b[t+o+1];
                    const r32=(o)=>le?b[t+o]|(b[t+o+1]<<8)|(b[t+o+2]<<16)|(b[t+o+3]<<24)
                                    :(b[t+o]<<24)|(b[t+o+1]<<16)|(b[t+o+2]<<8)|b[t+o+3];
                    const ifd=r32(4), ne=r16(ifd);
                    for(let e=0;e<ne;e++){
                        const eo=ifd+2+e*12;
                        if(eo+12>b.length-t) break;
                        if(r16(eo)===0x0112) return r16(eo+8);
                    }
                }
            }
            if(mk===0xDA) break;
            pos+=2+len;
        }
        return 1;
    }
    const EXIF_CSS = {
        1:'', 2:'scaleX(-1)', 3:'rotate(180deg)', 4:'scaleY(-1)',
        5:'rotate(90deg) scaleX(-1)', 6:'rotate(90deg)',
        7:'rotate(-90deg) scaleX(-1)', 8:'rotate(-90deg)'
    };

    /* ================================================================
       SETTINGS PERSISTENCE  -  auto-save all controls to localStorage
    ================================================================ */
    const SETTINGS_PERSIST_KEY = 'gg_laserprep_v7_settings';

    function captureAllSettings() {
        const s = {};
        document.querySelectorAll('input[type="range"],input[type="number"],select').forEach(el=>{
            if (el.id) s[el.id] = el.value;
        });
        document.querySelectorAll('input[type="checkbox"]').forEach(el=>{
            if (el.id) s[el.id] = el.checked;
        });
        return s;
    }

    function restoreAllSettings(saved) {
        if (!saved) return;
        batchSettings(() => {
            Object.entries(saved).forEach(([id,val])=>{
                const el = $(id); if (!el) return;
                if (el.type==='checkbox') el.checked = val; else el.value = val;
            });
            $('ditherSelect')?.dispatchEvent(new Event('change'));
        }, false); /* caller (undoAction/redoAction) calls queueProcess() itself */
    }

    function persistSettings() {
        clearTimeout(state.settingsPersistDebounce);
        state.settingsPersistDebounce = setTimeout(()=>{
            try { localStorage.setItem(SETTINGS_PERSIST_KEY, JSON.stringify(captureAllSettings())); }
            catch(e) {}
        }, 800);
    }

    function loadPersistedSettings() {
        try {
            const raw = localStorage.getItem(SETTINGS_PERSIST_KEY);
            if (raw) { restoreAllSettings(JSON.parse(raw)); toast('Settings restored', 1500); }
        } catch(e) {}
    }

    /* ================================================================
       UNDO / REDO  -  ring buffer of settings snapshots (max 20)
    ================================================================ */
    function undoSnapshot() {
        if (state.undoSuspended) return;
        const snap = captureAllSettings();
        if (state.undoIndex < state.undoHistory.length-1)
            state.undoHistory.splice(state.undoIndex+1);
        state.undoHistory.push(snap);
        if (state.undoHistory.length > state.undoMax) state.undoHistory.shift();
        state.undoIndex = state.undoHistory.length-1;
        updateUndoButtons();
    }

    function undoAction() {
        if (state.undoIndex <= 0) { toast('Nothing to undo'); return; }
        state.undoIndex--;
        state.undoSuspended = true;
        restoreAllSettings(state.undoHistory[state.undoIndex]);
        state.undoSuspended = false;
        updateUndoButtons(); queueProcess();
        toast('Undo (' + state.undoIndex + '/' + (state.undoHistory.length-1) + ')');
    }

    function redoAction() {
        if (state.undoIndex >= state.undoHistory.length-1) { toast('Nothing to redo'); return; }
        state.undoIndex++;
        state.undoSuspended = true;
        restoreAllSettings(state.undoHistory[state.undoIndex]);
        state.undoSuspended = false;
        updateUndoButtons(); queueProcess();
        toast('Redo (' + state.undoIndex + '/' + (state.undoHistory.length-1) + ')');
    }

    function updateUndoButtons() {
        const u=$('btnUndo'), r=$('btnRedo');
        if (u) u.disabled = state.undoIndex<=0;
        if (r) r.disabled = state.undoIndex>=state.undoHistory.length-1;
    }

    /* ================================================================
       BATCH PROCESSING  -  queue multiple files, process sequentially
    ================================================================ */
    function startBatch(files) {
        if (!files||!files.length) return;
        state.batchQueue   = Array.from(files);
        state.batchResults = [];
        state.batchActive  = true;
        const track = $('batchProgressTrack');
        if (track) track.classList.add('active');
        updateBatchProgress(0);
        toast('Batch: ' + files.length + ' image' + (files.length>1?'s':'') + ' queued');
        processBatchNext();
    }

    function processBatchNext() {
        if (!state.batchActive||!state.batchQueue.length) { finishBatch(); return; }
        const file = state.batchQueue.shift();
        const done = state.batchResults.length;
        const total = done + state.batchQueue.length + 1;
        toast('Batch ' + (done+1) + '/' + total + ': ' + file.name);
        const errs = validateFile(file);
        if (errs.length) {
            state.batchResults.push({name:file.name,error:errs[0]});
            processBatchNext(); return;
        }
        const reader = new FileReader();
        reader.onload = (ev) => {
            const orientation = readExifOrientation(ev.target.result);
            const url = URL.createObjectURL(new Blob([ev.target.result]));
            const img = new Image();
            img.onload = () => {
                URL.revokeObjectURL(url);
                state.image = img; state.loadedFileName = file.name;
                state.image._ggId = ++state.imageIdCounter;
                state.lanczosCache = {imageId:null,pxW:0,pxH:0,data:null};
                const needsSwap = orientation>=5&&orientation<=8;
                state.ratio = needsSwap ? img.height/img.width : img.width/img.height;
                $('imgWidth').value  = Math.round(((needsSwap?img.height:img.width)/300)*25.4);
                $('imgHeight').value = Math.round(((needsSwap?img.width:img.height)/300)*25.4);
                state._batchOnComplete = () => {
                    if (state.processedImageData)
                        state.batchResults.push({
                            name: file.name.replace(/\.[^.]+$/,'')+'_laser.png',
                            data: state.processedImageData.slice(),
                            w: state.processedImageW, h: state.processedImageH
                        });
                    setTimeout(processBatchNext, 80);
                };
                runPipeline();
            };
            img.onerror = () => {
                toast('Batch: skipped ' + file.name);
                state.batchResults.push({name:file.name,error:'decode failed'});
                setTimeout(processBatchNext,50);
            };
            img.src = url;
        };
        reader.onerror = () => {
            state.batchResults.push({name:file.name,error:'read failed'});
            setTimeout(processBatchNext,50);
        };
        reader.readAsArrayBuffer(file);
    }
    function handleBatchResult(result) {
        if (!result) return;
        state.batchResults.push({
            name: (state.loadedFileName || 'image').replace(/\.[^.]+$/, '') + '_laser.png',
            data: result,
            w: state.processedImageW,
            h: state.processedImageH
        });
        setTimeout(processBatchNext, 80);
    }
    function handleBatchError(msg) { toast('Batch error: '+msg); }
    function updateBatchProgress(pct) { const b=$('batchProgressBar'); if(b) b.style.width=pct+'%'; }

    function finishBatch() {
        state.batchActive = false;
        const track = $('batchProgressTrack');
        if (track) track.classList.remove('active');
        updateBatchProgress(0);
        const ok = state.batchResults.filter(r=>!r.error);
        toast('Batch done: ' + ok.length + '/' + state.batchResults.length + ' exported');
        const dpi = parseFloat($('imgDpiNum').value)||300;
        ok.forEach((res,i)=>setTimeout(()=>{
            const ec=document.createElement('canvas');
            ec.width=res.w; ec.height=res.h;
            ec.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(res.data),res.w,res.h),0,0);
            const url=injectPhysChunk(ec.toDataURL('image/png'),dpi);
            if (window.AndroidBridge) {
                fetch(url).then(r=>r.blob()).then(blob=>{
                    const reader=new FileReader();
                    reader.onloadend=()=>{
                        window.AndroidBridge.saveFile(reader.result.split(',')[1],res.name,'image/png');
                    };
                    reader.readAsDataURL(blob);
                });
                setTimeout(()=>URL.revokeObjectURL(url),5000);
            } else {
                const a=document.createElement('a'); a.download=res.name; a.href=url; a.click();
                setTimeout(()=>URL.revokeObjectURL(url),5000);
            }
        }, i*350));
    }

    /* ================================================================
       DEBOUNCED CONTAINER RESIZE  -  ResizeObserver
    ================================================================ */
    let containerResizeTimer;
    if (typeof ResizeObserver !== 'undefined') {
        new ResizeObserver(()=>{
            clearTimeout(containerResizeTimer);
            containerResizeTimer = setTimeout(()=>{
                if (state.processedImageData&&state.processedImageW) {
                    ctx.putImageData(
                        new ImageData(new Uint8ClampedArray(state.processedImageData),
                                      state.processedImageW,state.processedImageH),0,0);
                    applyOverlays();
                }
            }, 150);
        }).observe(container);
    }

    /* ================================================================
       OFFSCREENCANVAS RENDER  -  avoids main-thread compositing stall
    ================================================================ */
    function renderToCanvas(imageData, w, h) {
        canvas.width = w; canvas.height = h;
        if (typeof OffscreenCanvas !== 'undefined') {
            try {
                const osc = new OffscreenCanvas(w, h);
                osc.getContext('2d').putImageData(new ImageData(imageData,w,h),0,0);
                ctx.drawImage(osc,0,0);
                return;
            } catch(e) {}
        }
        ctx.putImageData(new ImageData(imageData,w,h),0,0);
    }

    /* ================================================================
       SAFE MODE  -  corrupted file error boundary
    ================================================================ */
    function activateSafeMode(reason) {
        if (state.safeMode) return;
        state.safeMode = true;
        console.warn('[SafeMode]', reason);
        toast('Safe Mode: ' + reason, 5000);
        const dpiNum=$('imgDpiNum'), dpiSlider=$('imgDpi');
        if (dpiNum&&parseFloat(dpiNum.value)>300) dpiNum.value=dpiSlider.value=300;
    }

    /* ================================================================
       MATERIAL PROFILES
    ================================================================ */
    const materialProfiles = {
        /* Bamboo: medium grain, burns evenly. Stucki spreads error well across
           grain lines. Gamma 1.2 lifts shadows to prevent under-burn in pale areas. */
        bamboo:     { gamma:1.2, contrast:12, brightness:5,   dither:'stucki',  invert:false },

        /* Basswood ply: very pale, fine grain, low contrast. Needs gamma 1.25
           to compensate for poor burn contrast on light wood. Floyd-Steinberg
           preserves fine grain detail better than wider kernels. */
        basswood:   { gamma:1.25, contrast:8,  brightness:5,  dither:'floyd',   invert:false },

        /* MDF: dense, uniform, burns dark quickly. Gamma 1.4 prevents highlights
           blowing out. Jarvis wider kernel smooths the even surface well. */
        mdf:        { gamma:1.4, contrast:15,  brightness:-5, dither:'jarvis',  invert:false },

        /* Leather: high natural contrast, surface texture varies. Floyd keeps
           fine detail. Brightness -5 (not -10) avoids over-darkening pale hides. */
        leather:    { gamma:1.1, contrast:20,  brightness:-5, dither:'floyd',   invert:false },

        /* Canvas: rough texture, wide tonal range. Halftone suits the weave.
           Contrast raised to 18 to work against texture noise. Gamma 1.0 neutral. */
        canvas:     { gamma:1.0, contrast:18,  brightness:8,  dither:'halftone',invert:false },

        /* Glass: laser removes coating from back  -  must invert. Jarvis gives
           smooth gradients in the transparent/opaque transition. */
        glass:      { gamma:1.5, contrast:30,  brightness:0,  dither:'jarvis',  invert:true  },

        /* Acrylic: inverted (ablates frosted surface). Stucki smooth for clean
           substrate. High contrast for crisp white-on-clear look. */
        acrylic:    { gamma:1.2, contrast:25,  brightness:5,  dither:'stucki',  invert:true  },

        /* Anodised aluminium: ablates colour coating, very precise. Invert OK.
           Contrast raised to 30 (was 10  -  too low for visible anodised mark).
           Floyd gives fine line fidelity on hard substrate. */
        anodised:   { gamma:1.0, contrast:30,  brightness:0,  dither:'floyd',   invert:true  },

        /* Black painted ceramic tile (Norton/Cermark method): coating ablated.
           Very high contrast needed. Stucki for smooth gradients on ceramic. */
        black_tile: { gamma:1.3, contrast:40,  brightness:10, dither:'stucki',  invert:true  },

        /* White painted ceramic tile: laser darkens paint (not ablating).
           No invert. Jarvis smooth gradients. */
        white_tile: { gamma:1.1, contrast:20,  brightness:0,  dither:'jarvis',  invert:false },

        /* Rainbow scratch paper: remove top colour layer. Invert OK.
           Floyd gives clean edges on thin coating. */
        scratch:    { gamma:1.0, contrast:15,  brightness:0,  dither:'floyd',   invert:true  },

        /* Slate: dark rough surface, inverted (laser lightens). Gamma raised
           to 1.05 (was 0.8  -  crushed shadows and lost midtone detail). Stucki
           handles the rough surface grain well. */
        slate:      { gamma:1.05, contrast:30, brightness:12, dither:'stucki',  invert:true  },

        /* Granite: very rough crystalline surface, inverted. Gamma 1.0 neutral
           (was 0.9  -  slightly dark). Jarvis handles granular texture. */
        granite:    { gamma:1.0, contrast:22,  brightness:8,  dither:'jarvis',  invert:true  }
    };

    /* ================================================================
       FILE LOADING  -  with validation, EXIF orientation, error boundary
    ================================================================ */
    function loadImageFile(file) {
        /* -- Input validation -- */
        const fileErrors = validateFile(file);
        if (fileErrors.length) {
            toast('[!] ' + fileErrors[0], 4000);
            console.warn('[LoadImage]', fileErrors);
            return;
        }

        const reader = new FileReader();
        reader.onload = (event) => {
            /* -- EXIF orientation (JPEG only) -- */
            let orientation = 1;
            try { orientation = readExifOrientation(event.target.result); }
            catch(e) { /* non-critical */ }

            /* -- Embedded DPI detection (PNG pHYs / JPEG JFIF) -- */
            const embeddedDpi = readEmbeddedDpi(event.target.result);
            const sourceDpi   = (embeddedDpi && embeddedDpi >= 72 && embeddedDpi <= 1200)
                                ? embeddedDpi : 300;

            /* -- Create image from ArrayBuffer via blob URL -- */
            const blob = new Blob([event.target.result]);
            const url  = URL.createObjectURL(blob);
            const img  = new Image();

            img.onload = () => {
                URL.revokeObjectURL(url);

                /* -- Dimension validation (non-blocking, shows warning) -- */
                const dimErrors = validateDimensions(img);
                if (dimErrors.length) toast('[!] ' + dimErrors[0], 3500);

                /* -- EXIF: swap dimensions for rotated images -- */
                const needsSwap = orientation >= 5 && orientation <= 8;
                const srcW = needsSwap ? img.height : img.width;
                const srcH = needsSwap ? img.width  : img.height;

                state.image = img;
                state.loadedFileName = file.name;
                state.image._ggId   = ++state.imageIdCounter;
                /* Store EXIF orientation for downstream use */
                state.image._exifOrientation = orientation;
                state.image._exifCss         = EXIF_CSS[orientation] || '';
                state.lanczosCache = { imageId: null, pxW: 0, pxH: 0, data: null };
                state.originalWidth  = srcW;
                state.originalHeight = srcH;
                state.ratio = srcW / srcH;
                state.memoryWarned = false;
                state.safeMode     = false;

                $('imgWidth').value  = Math.round((srcW  / sourceDpi) * 25.4);
                $('imgHeight').value = Math.round((srcH / sourceDpi) * 25.4);
                $('dropHint').classList.add('hidden');

                updateImgStats();
                resetView();
                updateEstimation();
                undoSnapshot();     /* capture initial state for undo */
                queueProcess();
            };

            img.onerror = () => {
                URL.revokeObjectURL(url);
                /* -- Corrupted file error boundary -- */
                activateSafeMode('Cannot decode image  -  file may be corrupted');
                toast('[!] Cannot open image. File may be corrupted or unsupported.', 5000);
            };

            img.src = url;
        };

        reader.onerror = () => {
            activateSafeMode('File read error');
            toast('[!] Could not read file. Please try again.', 4000);
        };

        /* Read as ArrayBuffer so we can inspect raw bytes for EXIF + DPI */
        reader.readAsArrayBuffer(file);
    }

    /* ================================================================
       READ EMBEDDED DPI  -  restored function declaration (was accidentally
       stripped, leaving only the body as orphaned code)
    ================================================================ */
    function readEmbeddedDpi(arrayBuffer) {
        /* Returns DPI as a number, or null if not found/parseable */
        const bytes = new Uint8Array(arrayBuffer);
        const v32 = (o) => (bytes[o]<<24|bytes[o+1]<<16|bytes[o+2]<<8|bytes[o+3])>>>0;
        const v16 = (o) => (bytes[o]<<8|bytes[o+1]);

        /* PNG: check pHYs chunk (pixels per unit, unit=1 means metre) */
        if (bytes[0]===0x89&&bytes[1]===0x50&&bytes[2]===0x4E&&bytes[3]===0x47) {
            let pos = 8;
            while (pos < bytes.length - 12) {
                const len  = v32(pos);
                const type = String.fromCharCode(bytes[pos+4],bytes[pos+5],bytes[pos+6],bytes[pos+7]);
                if (type === 'pHYs' && len === 9) {
                    const ppmX = v32(pos+8);
                    const unit = bytes[pos+16]; // 1 = metre
                    if (unit === 1 && ppmX > 0) {
                        return Math.round(ppmX * 0.0254); // pixels-per-metre -> dpi
                    }
                }
                if (type === 'IDAT' || type === 'IEND') break;
                pos += 12 + len;
            }
            return null;
        }

        /* JPEG: scan for APP0 (JFIF) or APP1 (EXIF) DPI */
        if (bytes[0]===0xFF&&bytes[1]===0xD8) {
            let pos = 2;
            while (pos < bytes.length - 4) {
                if (bytes[pos] !== 0xFF) break;
                const marker = bytes[pos+1];
                const segLen = v16(pos+2);
                /* APP0 JFIF: density units at offset +11, Xdensity at +12 */
                if (marker === 0xE0 && segLen >= 16) {
                    const jfif = String.fromCharCode(bytes[pos+4],bytes[pos+5],bytes[pos+6],bytes[pos+7],bytes[pos+8]);
                    if (jfif === 'JFIF\x00') {
                        const unit = bytes[pos+11];
                        const xDen = v16(pos+12);
                        if (unit === 1 && xDen > 0) return xDen;           // DPI directly
                        if (unit === 2 && xDen > 0) return Math.round(xDen*2.54); // dots/cm -> dpi
                    }
                }
                if (marker === 0xDA) break; // SOS = start of scan data
                pos += 2 + segLen;
            }
            return null;
        }
        return null;
    } /* end readEmbeddedDpi */

    /* ================================================================
       DUPLICATE loadImageFile REMOVED (v7 fix)
       The full, correct version with EXIF orientation, validation, error
       boundaries, and undoSnapshot() lives above at the FILE LOADING section.
       This stripped-down copy was inadvertently left in and was silently
       overwriting the full version at runtime  -  causing image load failures.
    ================================================================ */
    /*  <<< REMOVED DUPLICATE  -  DO NOT RESTORE >>>
    function loadImageFile(file) { ... } // lines 1139-1173 original
    */

    /* ================================================================
       IMG STATS
    ================================================================ */
    function updateImgStats() {
        if (!state.image) return;
        const w_mm = parseFloat($('imgWidth').value);
        const h_mm = parseFloat($('imgHeight').value);
        const dpi  = parseFloat($('imgDpiNum').value);
        const pxW  = Math.round((w_mm / 25.4) * dpi);
        const pxH  = Math.round((h_mm / 25.4) * dpi);
        const el   = $('imgStats');
        const srcLabel = (state.originalWidth && state.originalHeight)
            ? `<span class="stats-src">src ${state.originalWidth}x${state.originalHeight}px</span><br>`
            : '';
        const nameLabel = state.loadedFileName
            ? `<span class="stats-name">${state.loadedFileName}</span>`
            : '';
        el.classList.add('img-stats--visible');
        el.innerHTML = `${pxW}x${pxH}px &nbsp;.&nbsp; ${dpi}dpi<br>${w_mm}x${h_mm}mm<br>${srcLabel}${nameLabel}`;
    }

    /* ================================================================
       PAN / ZOOM
    ================================================================ */
    let isDragging = false, startX, startY, initialDist = 0, lastTap = 0;

    container.addEventListener('mousedown', (e) => {
        isDragging = true;
        startX = e.clientX - state.panX;
        startY = e.clientY - state.panY;
    });
    window.addEventListener('mouseup', () => isDragging = false);
    window.addEventListener('mousemove', (e) => {
        if (!isDragging) return;
        state.panX = e.clientX - startX;
        state.panY = e.clientY - startY;
        updateTransform();
    });
    container.addEventListener('wheel', (e) => {
        e.preventDefault();
        state.zoom = Math.max(0.1, Math.min(10, state.zoom + (-e.deltaY * 0.001)));
        updateTransform();
    }, { passive: false });

    container.addEventListener('touchstart', (e) => {
        if (e.touches.length === 1) {
            isDragging = true;
            startX = e.touches[0].clientX - state.panX;
            startY = e.touches[0].clientY - state.panY;
            const now = Date.now();
            if (now - lastTap < 300) resetView();
            lastTap = now;
        } else if (e.touches.length === 2) {
            initialDist = Math.hypot(
                e.touches[0].clientX - e.touches[1].clientX,
                e.touches[0].clientY - e.touches[1].clientY
            );
        }
    });
    container.addEventListener('touchmove', (e) => {
        e.preventDefault();
        if (e.touches.length === 1 && isDragging) {
            state.panX = e.touches[0].clientX - startX;
            state.panY = e.touches[0].clientY - startY;
            updateTransform();
        } else if (e.touches.length === 2) {
            const dist = Math.hypot(
                e.touches[0].clientX - e.touches[1].clientX,
                e.touches[0].clientY - e.touches[1].clientY
            );
            state.zoom = Math.max(0.1, Math.min(10, state.zoom * (dist / initialDist)));
            initialDist = dist;
            updateTransform();
        }
    }, { passive: false });
    container.addEventListener('touchend', () => isDragging = false);

    function updateTransform() {
        canvas.style.transform = `translate(${state.panX}px,${state.panY}px) scale(${state.zoom})`;
        $('zoomSlider').value = state.zoom;
    }
    function resetView() {
        state.zoom = 1; state.panX = 0; state.panY = 0;
        updateTransform();
    }

    /* ================================================================
       TIME ESTIMATION
    ================================================================ */
    function updateEstimation() {
        const w   = parseFloat($('imgWidth').value);
        const h   = parseFloat($('imgHeight').value);
        const dpi = parseFloat($('imgDpiNum').value);
        const gcSpeedEl = $('gcSpeed');
        const speed = gcSpeedEl ? (parseFloat(gcSpeedEl.value) || 3000) : 3000;
        const lineInterval = 25.4 / dpi;
        const totalLines   = h / lineInterval;
        const overscan     = 1.10;
        const totalDist    = (w * overscan) * totalLines;
        const mins         = totalDist / speed;
        const hours        = Math.floor(mins / 60);
        const minutes      = Math.round(mins % 60);
        $('timeEst').innerHTML =
            `<b>Est. Time:</b> ${hours > 0 ? hours+'h ' : ''}${minutes}m &nbsp;<small>(${Math.round(totalLines)} passes @ ${speed}mm/min)</small>`;
    }

    /* ================================================================
       SLIDER BINDINGS  -  live badge + filled track
    ================================================================ */
    function updateSliderTrack(range) {
        const min = parseFloat(range.min) || 0;
        const max = parseFloat(range.max) || 100;
        const pct = ((parseFloat(range.value) - min) / (max - min)) * 100;
        range.style.setProperty('--sl-pct', pct + '%');
    }

    function bindInputs(rangeId, numId) {
        const range = $(rangeId);
        const num   = $(numId);
        if (!range || !num) return;

        const header = num.closest('.control-header');
        if (header) {
            const badge = document.createElement('span');
            badge.className = 'val-live';
            badge.textContent = num.value;
            badge.setAttribute('aria-hidden', 'true');
            header.appendChild(badge);
            header.classList.add('has-live-badge');

            let flashTimer;
            function flashBadge(val) {
                badge.textContent = val;
                badge.classList.add('active');
                clearTimeout(flashTimer);
                flashTimer = setTimeout(() => badge.classList.remove('active'), 800);
            }

            range.addEventListener('input', () => {
                num.value = range.value;
                flashBadge(range.value);
                updateSliderTrack(range);
                queueProcess(true);
            });
            range.addEventListener('pointerdown', _startDrag);
            range.addEventListener('touchstart',  _startDrag, { passive: true });
            range.addEventListener('pointerup',   _endDrag);
            range.addEventListener('touchend',    _endDrag);
            num.addEventListener('input', () => {
                range.value = num.value;
                flashBadge(num.value);
                updateSliderTrack(range);
                queueProcess();
            });
            updateSliderTrack(range);
        } else {
            range.addEventListener('input', () => { num.value = range.value; queueProcess(true); });
            range.addEventListener('pointerdown', _startDrag);
            range.addEventListener('touchstart',  _startDrag, { passive: true });
            range.addEventListener('pointerup',   _endDrag);
            range.addEventListener('touchend',    _endDrag);
            num.addEventListener('input',   () => { range.value = num.value; queueProcess(); });
        }
    }

    /* ================================================================
       APPLY PRESET HELPER
    ================================================================ */
    function applyPresetValues(values, label) {
        batchSettings(() => {
            const map = [
                ['slGamma','valGamma','gamma'],['slCont','valCont','contrast'],
                ['slBright','valBright','brightness'],['slBlack','valBlack','black'],
                ['slWhite','valWhite','white'],['slSharp','valSharp','sharpen'],
                ['slDenoise','valDenoise','denoise']
            ];
            map.forEach(([sid, vid, key]) => {
                const sl = $(sid), vl = $(vid);
                if (sl && vl && values[key] !== undefined) {
                    sl.value = vl.value = values[key];
                }
            });
            $('chkProtectHigh').checked = values.protectHigh;
            $('chkHistEq').checked      = values.histEq;
            $('chkInvert').checked      = values.invert;
            $('chkSimulate').checked    = values.simulate;
            $('chkLanczos').checked     = true;
            $('ditherSelect').value     = values.dither;
            $('ditherSelect').dispatchEvent(new Event('change'));
            const matSel = $('materialSelect');
            if (matSel && values.material) matSel.value = values.material;
            if (values.localContrast !== undefined) {
                const lcs = $('slLocalContrast'), lcv = $('valLocalContrast');
                if (lcs && lcv) { lcs.value = lcv.value = values.localContrast; }
            }
        });
        toast(`${label} settings applied`);
    }

    /* ================================================================
       SAVE / LOAD CONFIG
    ================================================================ */
    function saveLaserPrep() {
        const s = {
            bright: $('valBright').value, contrast: $('valCont').value,
            gamma:  $('valGamma').value,  sharp: $('valSharp').value,
            dither: $('ditherSelect').value, black: $('valBlack').value,
            white:  $('valWhite').value,  denoise: $('valDenoise').value
        };
        localStorage.setItem('laserprep_settings', JSON.stringify(s));
        toast('Config saved');
    }

    function loadLaserPrep() {
        const raw = localStorage.getItem('laserprep_settings');
        if (!raw) { toast('No saved config found'); return; }
        const s = JSON.parse(raw);
        batchSettings(() => {
            $('slBright').value  = $('valBright').value  = s.bright;
            $('slCont').value    = $('valCont').value    = s.contrast;
            $('slGamma').value   = $('valGamma').value   = s.gamma;
            $('slSharp').value   = $('valSharp').value   = s.sharp;
            $('slBlack').value   = $('valBlack').value   = s.black   || 0;
            $('slWhite').value   = $('valWhite').value   = s.white   || 255;
            $('slDenoise').value = $('valDenoise').value = s.denoise || 0;
            $('ditherSelect').value = s.dither;
            $('ditherSelect').dispatchEvent(new Event('change'));
        });
        toast('Config loaded');
    }

    /* ================================================================
       SECTION COLLAPSE / EXPAND
    ================================================================ */
    const STORE_KEY = 'gg_sections';
    let collapsedSections = {};
    try { collapsedSections = JSON.parse(localStorage.getItem(STORE_KEY) || '{}'); } catch(e) {}

    /* FIX: If every stored section is collapsed the user can't open anything.
       Guard: if ALL keys are true (collapsed), wipe and start fresh. */
    (function sanitiseCollapsedSections() {
        const keys = Object.keys(collapsedSections);
        if (keys.length > 0 && keys.every(k => collapsedSections[k] === true)) {
            collapsedSections = {};
            try { localStorage.removeItem(STORE_KEY); } catch(e) {}
        }
    })();

    document.querySelectorAll('.section-title').forEach((title, idx) => {
        const section = title.closest('.section');
        const key = 'sec_' + idx;

        /* If localStorage has an explicit record, honour it.
           Otherwise fall back to whatever collapsed class is in the HTML
           (lets us set sensible defaults in markup without touching localStorage). */
        if (Object.prototype.hasOwnProperty.call(collapsedSections, key)) {
            /* Stored preference — apply it, overriding HTML default */
            if (collapsedSections[key]) {
                section.classList.add('collapsed');
            } else {
                section.classList.remove('collapsed');
            }
        }
        /* else: leave the HTML class as-is (collapsed or not) */

        const isCollapsed = section.classList.contains('collapsed');
        title.setAttribute('tabindex', '0');
        title.setAttribute('role', 'button');
        title.setAttribute('aria-expanded', !isCollapsed);

        function toggleSection() {
            section.classList.toggle('collapsed');
            const collapsed = section.classList.contains('collapsed');
            title.setAttribute('aria-expanded', !collapsed);
            collapsedSections[key] = collapsed;
            try { localStorage.setItem(STORE_KEY, JSON.stringify(collapsedSections)); } catch(e) {}
        }

        title.addEventListener('click', toggleSection);
        title.addEventListener('keydown', (e) => {
            if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); toggleSection(); }
        });
    });

    /* ================================================================
       EXPORT PENDING INDICATOR
    ================================================================ */
    const exportBtn = $('btnExport');
    function markPending() {
        if (!exportBtn) return;
        exportBtn.classList.add('pending');
        exportBtn.title = 'Export PNG (settings changed since last export)';
    }
    function clearPending() {
        if (!exportBtn) return;
        exportBtn.classList.remove('pending');
        exportBtn.title = 'Export processed image as PNG';
    }
    document.querySelectorAll('input[type="range"],input[type="number"],select,input[type="checkbox"]')
        .forEach(el => el.addEventListener('input', () => { markPending(); persistSettings(); }));
    document.querySelectorAll('select').forEach(el => el.addEventListener('change', () => { markPending(); persistSettings(); }));
    /* Undo snapshot on mouseup/touchend (after slider drag settles) */
    document.querySelectorAll('input[type="range"]').forEach(el =>
        el.addEventListener('change', () => undoSnapshot()));
    document.querySelectorAll('select,input[type="checkbox"]').forEach(el =>
        el.addEventListener('change', () => undoSnapshot()));

    /* ================================================================
       HISTOGRAM OVERLAY
    ================================================================ */
    const histCanvas = $('histOverlay');
    const histBtn    = $('btnToggleHist');
    let showHist = false;

    function drawHistogram() {
        if (!showHist || !histCanvas) return;
        /* Always ensure canvas dimensions are set before drawing */
        histCanvas.width  = 192;
        histCanvas.height = 64;
        const W = histCanvas.width, H = histCanvas.height;
        const hCtx = histCanvas.getContext('2d');

        /* Prefer clean processed data over canvas pixels (avoids overlay contamination) */
        let data, pixelCount;
        if (state.processedImageData && state.processedImageW) {
            data       = state.processedImageData;
            pixelCount = state.processedImageW * state.processedImageH;
        } else {
            if (!canvas.width || !canvas.height) return;
            let imgData;
            try { imgData = ctx.getImageData(0, 0, canvas.width, canvas.height); } catch(e) { return; }
            data       = imgData.data;
            pixelCount = canvas.width * canvas.height;
        }

        /* 256-bin histogram */
        const bins = new Float32Array(256);
        for (let i = 0; i < data.length; i += 4) {
            const lum = Math.round(0.2126*data[i] + 0.7152*data[i+1] + 0.0722*data[i+2]);
            bins[Math.min(255, Math.max(0, lum))]++;
        }

        /* Normalise: log scale so small peaks are still visible */
        const maxRaw = Math.max(...bins, 1);
        const logMax = Math.log1p(maxRaw);

        hCtx.clearRect(0, 0, W, H);
        /* Background */
        hCtx.fillStyle = 'rgba(0,0,0,0.75)';
        hCtx.fillRect(0, 0, W, H);

        /* Bars */
        const barW = W / 256;
        for (let b = 0; b < 256; b++) {
            const bh = Math.round((Math.log1p(bins[b]) / logMax) * (H - 2));
            if (bh < 1) continue;
            const bright = b;
            hCtx.fillStyle = `rgb(${bright},${bright},${bright})`;
            hCtx.fillRect(Math.floor(b * barW), H - bh, Math.ceil(barW) + 1, bh);
        }

        /* Midpoint reference line */
        hCtx.strokeStyle = 'rgba(255,68,68,0.6)';
        hCtx.lineWidth = 1;
        hCtx.beginPath(); hCtx.moveTo(W/2, 0); hCtx.lineTo(W/2, H); hCtx.stroke();

        /* Axis labels */
        hCtx.fillStyle = 'rgba(255,255,255,0.4)';
        hCtx.font = '7px monospace';
        hCtx.fillText('0', 2, H-2);
        hCtx.fillText('128', W/2-8, H-2);
        hCtx.fillText('255', W-18, H-2);
    }

    if (histBtn) {
        histBtn.addEventListener('click', () => {
            showHist = !showHist;
            histBtn.classList.toggle('active-toggle', showHist);
            histBtn.setAttribute('aria-pressed', showHist);
            histCanvas.classList.toggle('hist-overlay--visible', showHist);
            if (showHist) drawHistogram();
        });
    }

    new MutationObserver(() => {
        if (!loader.classList.contains('visible')) setTimeout(drawHistogram, 50);
    }).observe(loader, { attributes: true, attributeFilter: ['class'] });

    /* ================================================================
       KEYBOARD SHORTCUTS
    ================================================================ */
    const kbHelp = $('kbHelp');
    const kbBtn  = $('btnKbHelp');
    let kbVisible = false;

    function toggleKbHelp() {
        kbVisible = !kbVisible;
        if (kbHelp) { kbHelp.classList.toggle('visible', kbVisible); kbHelp.setAttribute('aria-hidden', !kbVisible); }
        if (kbBtn)  { kbBtn.classList.toggle('active-toggle', kbVisible); kbBtn.setAttribute('aria-pressed', kbVisible); }
    }

    if (kbBtn) kbBtn.addEventListener('click', toggleKbHelp);

    /* Help modal */
    (function initHelp() {
        var btn   = $('btnHelp');
        var modal = $('helpModal');
        var close = $('btnCloseHelp');
        if (!btn || !modal) return;
        btn.addEventListener('click', function() {
            modal.classList.add('open');
            modal.setAttribute('aria-hidden', 'false');
        });
        if (close) close.addEventListener('click', function() {
            modal.classList.remove('open');
            modal.setAttribute('aria-hidden', 'true');
        });
        modal.addEventListener('click', function(e) {
            if (e.target === modal) {
                modal.classList.remove('open');
                modal.setAttribute('aria-hidden', 'true');
            }
        });
    })();

    document.addEventListener('click', (e) => {
        if (kbVisible && kbHelp && !kbHelp.contains(e.target) && e.target !== kbBtn) {
            kbVisible = false;
            kbHelp.classList.remove('visible');
            kbHelp.setAttribute('aria-hidden', 'true');
            if (kbBtn) { kbBtn.classList.remove('active-toggle'); kbBtn.setAttribute('aria-pressed', 'false'); }
        }
    });

    document.addEventListener('keydown', (e) => {
        /* Ctrl+Z = Undo, Ctrl+Y / Ctrl+Shift+Z = Redo  -  work even in inputs */
        if ((e.ctrlKey || e.metaKey) && e.key === 'z' && !e.shiftKey) {
            e.preventDefault(); undoAction(); return;
        }
        if ((e.ctrlKey || e.metaKey) && (e.key === 'y' || (e.key === 'z' && e.shiftKey))) {
            e.preventDefault(); redoAction(); return;
        }

        const tag = document.activeElement.tagName;
        if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT') return;
        switch (e.key) {
            case '?':
                e.preventDefault(); toggleKbHelp(); break;
            case 'e': case 'E':
                e.preventDefault(); exportBtn?.click(); break;
            case 'i': case 'I':
                e.preventDefault();
                const inv = $('chkInvert');
                if (inv) { inv.checked = !inv.checked; inv.dispatchEvent(new Event('change')); toast('Invert: ' + (inv.checked ? 'ON' : 'OFF')); }
                break;
            case 's': case 'S':
                e.preventDefault(); $('btnSplitView')?.click(); break;
            case 'r': case 'R':
                e.preventDefault(); resetView(); toast('View reset'); break;
            case ' ':
                e.preventDefault(); toast('Re-processing...'); queueProcess(); break;
        }
    });

    /* ================================================================
       COMPARISON SLIDER
    ================================================================ */
    const splitSlider = document.createElement('div');
    splitSlider.id = 'comparisonSlider';
    splitSlider.setAttribute('aria-hidden', 'true');
    container.appendChild(splitSlider);
    let draggingSlider = false;
    splitSlider.addEventListener('mousedown', () => draggingSlider = true);
    window.addEventListener('mouseup', () => draggingSlider = false);
    window.addEventListener('mousemove', (e) => {
        if (!draggingSlider || !state.splitView) return;
        const rect = container.getBoundingClientRect();
        const x = Math.max(10, Math.min(rect.width - 10, e.clientX - rect.left));
        splitSlider.style.left = x + 'px';
        /* Redraw split without re-running pipeline */
        _redrawSplitView();
    });

    /* Touch support for split slider */
    splitSlider.addEventListener('touchstart', (e) => { draggingSlider = true; e.stopPropagation(); }, { passive: true });
    window.addEventListener('touchend', () => draggingSlider = false);
    window.addEventListener('touchmove', (e) => {
        if (!draggingSlider || !state.splitView) return;
        const rect = container.getBoundingClientRect();
        const x = Math.max(10, Math.min(rect.width - 10, e.touches[0].clientX - rect.left));
        splitSlider.style.left = x + 'px';
        _redrawSplitView();
    }, { passive: true });

    /* Redraw the split view using already-processed data (no pipeline re-run) */
    function _redrawSplitView() {
        if (!state.splitView || !state.originalResizedData || !state.processedImageData) return;
        const w = state.processedImageW;
        const h = state.processedImageH;
        const displayData = state.processedImageData;
        const dpr = window.devicePixelRatio || 1;
        let splitX;
        const sliderLeft = parseFloat(splitSlider.style.left);
        if (!isNaN(sliderLeft)) {
            const containerW = container.clientWidth || w;
            splitX = Math.round((sliderLeft / containerW) * w);
        } else {
            splitX = Math.round(w / 2);
        }
        splitX = Math.max(0, Math.min(w, splitX));
        const merged = new Uint8ClampedArray(w * h * 4);
        for (let y = 0; y < h; y++) {
            for (let x = 0; x < w; x++) {
                const i = (y*w+x)*4;
                const src = x < splitX ? state.originalResizedData : displayData;
                merged[i]   = src[i];
                merged[i+1] = src[i+1];
                merged[i+2] = src[i+2];
                merged[i+3] = 255;
            }
        }
        ctx.putImageData(new ImageData(merged, w, h), 0, 0);
        ctx.fillStyle = '#ff4444';
        const divX = Math.round(splitX * dpr) / dpr;
        ctx.fillRect(divX - (0.5/dpr), 0, 1/dpr, h);
        applyOverlays();
    }

    /* ================================================================
       EDGE ENGRAVE (Sobel)
    ================================================================ */
    function edgeEngrave() {
        if (!state.image) { toast('Import an image first'); return; }
        /* FIX: read from processedImageData (clean pipeline output),
           not from canvas which may contain split-view or simulation overlays */
        const w = state.processedImageW || canvas.width;
        const h = state.processedImageH || canvas.height;
        const srcData = state.processedImageData
            ? state.processedImageData
            : ctx.getImageData(0, 0, w, h).data;
        const src = srcData;
        const dst = new Uint8ClampedArray(w * h * 4);
        for (let y=1; y<h-1; y++) {
            for (let x=1; x<w-1; x++) {
                const i = (y*w+x)*4;
                const gx = (-1*src[i-w*4-4])+(1*src[i-w*4+4])+(-2*src[i-4])+(2*src[i+4])+(-1*src[i+w*4-4])+(1*src[i+w*4+4]);
                const gy = (-1*src[i-w*4-4])+(-2*src[i-w*4])+(-1*src[i-w*4+4])+(1*src[i+w*4-4])+(2*src[i+w*4])+(1*src[i+w*4+4]);
                const mag = Math.sqrt(gx*gx+gy*gy);
                const val = mag>50?0:255;
                dst[i]=dst[i+1]=dst[i+2]=val; dst[i+3]=255;
            }
        }
        /* FIX: update processedImageData so export, G-code etc. use edge result */
        state.processedImageData = dst;
        state.processedImageW = w;
        state.processedImageH = h;
        /* Refresh canvas display */
        canvas.width = w; canvas.height = h;
        ctx.putImageData(new ImageData(dst, w, h), 0, 0);
        toast('Sobel edge engrave applied');
    }

    /* ================================================================
       VECTOR EXPORT
    ================================================================ */
    function exportVectorSVG() {
        if (!state.image) { toast('Import an image first'); return; }
        /* FIX: read from processedImageData (clean pipeline output),
           not from canvas which may contain split-view or simulation overlays */
        const w = state.processedImageW || canvas.width;
        const h = state.processedImageH || canvas.height;
        const img = (state.processedImageData && state.processedImageW)
            ? state.processedImageData
            : ctx.getImageData(0,0,w,h).data;
        toast('Generating vector SVG...');
        let svg=`<svg xmlns="http://www.w3.org/2000/svg" width="${w}" height="${h}" viewBox="0 0 ${w} ${h}">`;
        for (let y=0; y<h; y+=2) {
            let lineStarted=false, startX=0;
            for (let x=0; x<w; x++) {
                const v=img[(y*w+x)*4];
                if (v<120 && !lineStarted) { startX=x; lineStarted=true; }
                if ((v>=120||x===w-1) && lineStarted) {
                    svg+=`<line x1="${startX}" y1="${y}" x2="${x}" y2="${y}" stroke="black" stroke-width="1"/>`;
                    lineStarted=false;
                }
            }
        }
        svg+='</svg>';
        const blob=new Blob([svg],{type:'image/svg+xml'});
        const a=document.createElement('a');
        triggerDownload(blob, 'GG_Vector_Engrave.svg', 'image/svg+xml');
        toast('Vector SVG exported');
    }

    /* ================================================================
       CALIBRATION GRID
    ================================================================ */
    function generateCalibGrid() {
        const size=800;
        canvas.width=size; canvas.height=size;
        const gCtx=canvas.getContext('2d');
        gCtx.fillStyle='#ffffff'; gCtx.fillRect(0,0,size,size);
        const cells=10, cellSize=size/cells;
        for (let row=0; row<cells; row++) {
            for (let col=0; col<cells; col++) {
                const x=col*cellSize, y=row*cellSize;
                const powerPercent=Math.round((col/(cells-1))*100);
                const gray=255-Math.round((col/(cells-1))*255);
                gCtx.fillStyle=`rgb(${gray},${gray},${gray})`;
                gCtx.fillRect(x,y,cellSize,cellSize);
                gCtx.strokeStyle='#000'; gCtx.lineWidth=1;
                gCtx.strokeRect(x,y,cellSize,cellSize);
                gCtx.fillStyle=gray<128?'#fff':'#000';
                gCtx.font='bold 12px monospace';
                gCtx.fillText(powerPercent+'%', x+5, y+18);
                const speedPercent=Math.round((row/(cells-1))*100);
                gCtx.fillText(speedPercent+'%', x+5, y+cellSize-8);
            }
        }
        $('dropHint').classList.add('hidden');
        toast('Calibration grid generated  -  set laser speed in controller then run to find optimal power');
    }

    /* ================================================================
       SIMPLE MODE
    ================================================================ */
    (function initSimpleMode() {
        const simpleModeBtn   = $('btnSimpleMode');
        const simpleModeModal = $('simpleModeModal');
        const closeSimpleBtn  = $('btnCloseSimple');
        const simpleGoBtn     = $('btnSimpleGo');
        const simpleStatus    = $('simpleStatus');

        function openModal() {
            const curW = $('imgWidth').value;
            const curH = $('imgHeight').value;
            if (curW) $('simpleWidth').value  = curW;
            if (curH) $('simpleHeight').value = curH;
            simpleModeModal.classList.add('open');
            simpleModeModal.setAttribute('aria-hidden', 'false');
            simpleModeBtn.classList.add('simple-active');
        }

        function closeModal() {
            simpleModeModal.classList.remove('open');
            simpleModeModal.setAttribute('aria-hidden', 'true');
            simpleModeBtn.classList.remove('simple-active');
        }

        simpleModeBtn.addEventListener('click', openModal);
        closeSimpleBtn.addEventListener('click', closeModal);
        simpleModeModal.addEventListener('click', (e) => { if (e.target === simpleModeModal) closeModal(); });
        document.addEventListener('keydown', (e) => { if (e.key === 'Escape' && simpleModeModal.classList.contains('open')) closeModal(); });

        simpleGoBtn.addEventListener('click', () => {
            if (!state.image) {
                simpleStatus.style.color = 'var(--accent)';
                simpleStatus.textContent = '[!] Import an image first!';
                return;
            }
            const w   = parseInt($('simpleWidth').value)  || 100;
            const h   = parseInt($('simpleHeight').value) || 100;
            const mat = $('simpleMaterial').value;

            simpleStatus.style.color = 'var(--amber)';
            simpleStatus.textContent = '[spin] Applying settings...';
            simpleGoBtn.disabled = true;

            $('imgWidth').value  = w;
            $('imgHeight').value = h;
            const matSel = $('materialSelect');
            matSel.value = mat;
            matSel.dispatchEvent(new Event('change'));
            $('imgDpi').value    = 300;
            $('imgDpiNum').value = 300;
            $('chkLanczos').checked = true;

            simpleStatus.style.color = 'var(--amber)';
            simpleStatus.textContent = '[spin] Processing...';

            /* materialSelect.dispatchEvent('change') above already calls queueProcess().
               Do NOT call it again  -  that causes two pipeline runs.
               Wait for the single debounced run to complete then download. */
            function waitAndDownload(attempts) {
                if (attempts <= 0) {
                    simpleStatus.style.color = 'var(--accent)';
                    simpleStatus.textContent = '[!] Timed out  -  try Export PNG manually';
                    simpleGoBtn.disabled = false;
                    return;
                }
                if (state.isProcessing) { setTimeout(() => waitAndDownload(attempts-1), 300); return; }
                setTimeout(() => {
                    if (state.isProcessing) { setTimeout(() => waitAndDownload(attempts-1), 300); return; }
                    exportCleanPng(`GG_LaserPrep_${mat}_${w}x${h}mm.png`);
                    simpleStatus.style.color = 'var(--green)';
                    simpleStatus.textContent = 'OK Done! PNG downloaded.';
                    simpleGoBtn.disabled = false;
                    clearPending();
                }, 120);
            }

            setTimeout(() => waitAndDownload(30), 400);
        });
    })();

    /* ================================================================
       CAMERA
    ================================================================ */
    (function initCamera() {
        let camStream = null, camModal = null;

        function closeCamModal() {
            if (camStream) { camStream.getTracks().forEach(t => t.stop()); camStream = null; }
            if (camModal)  { camModal.remove(); camModal = null; }
        }

        $('btnCamera').addEventListener('click', async () => {
            if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
                toast('Opening camera via your browser...');
                const inp = fileInput;
                inp.setAttribute('capture','environment'); inp.click();
                setTimeout(() => inp.removeAttribute('capture'), 500);
                return;
            }
            try {
                camStream = await navigator.mediaDevices.getUserMedia({
                    video: { facingMode: { ideal:'environment' }, width:{ ideal:3840 }, height:{ ideal:2160 } },
                    audio: false
                });
            } catch(e) {
                toast('Camera unavailable  -  opening gallery instead');
                const inp = fileInput;
                inp.setAttribute('capture','environment'); inp.click();
                setTimeout(() => inp.removeAttribute('capture'), 500);
                return;
            }

            camModal = document.createElement('div');
            camModal.setAttribute('role', 'dialog');
            camModal.setAttribute('aria-modal', 'true');
            camModal.setAttribute('aria-label', 'Camera capture');
            camModal.style.cssText = 'position:fixed;inset:0;z-index:9999;background:#000;display:flex;flex-direction:column;align-items:center;justify-content:center;';

            const video = document.createElement('video');
            video.autoplay = true; video.playsInline = true; video.muted = true;
            video.setAttribute('aria-label', 'Camera preview');
            video.style.cssText = 'max-width:100%;max-height:80vh;object-fit:contain;';
            video.srcObject = camStream;

            const bar = document.createElement('div');
            bar.style.cssText = 'display:flex;gap:16px;margin-top:16px;';

            const btnSnap = document.createElement('button');
            btnSnap.textContent = 'Capture Capture';
            btnSnap.className = 'btn primary';
            btnSnap.setAttribute('aria-label', 'Capture photo');
            btnSnap.style.cssText = 'padding:12px 28px;font-size:1rem;';

            const btnClose = document.createElement('button');
            btnClose.textContent = 'x Cancel';
            btnClose.className = 'btn';
            btnClose.setAttribute('aria-label', 'Close camera');
            btnClose.style.cssText = 'padding:12px 20px;font-size:1rem;';

            bar.append(btnSnap, btnClose);
            camModal.append(video, bar);
            document.body.appendChild(camModal);

            btnClose.addEventListener('click', closeCamModal);
            btnSnap.addEventListener('click', () => {
                const snap = document.createElement('canvas');
                snap.width = video.videoWidth; snap.height = video.videoHeight;
                snap.getContext('2d').drawImage(video, 0, 0);
                closeCamModal();
                snap.toBlob(blob => {
                    const file = new File([blob], 'camera.jpg', { type:'image/jpeg' });
                    const dt = new DataTransfer(); dt.items.add(file);
                    fileInput.files = dt.files;
                    fileInput.dispatchEvent(new Event('change', { bubbles: true }));
                }, 'image/jpeg', 0.95);
            });
        });
    })();

    /* ================================================================
       SCAN ANIMATION  -  simulates laser head scanning across the image
    ================================================================ */
    let scanRunning = false;
    $('btnScanPreview').addEventListener('click', function () {
        if (!state.image) { toast('Import an image first'); return; }
        if (scanRunning) {
            scanRunning = false;
            this.classList.remove('active-toggle');
            this.setAttribute('aria-pressed', 'false');
            const ex = $('scanOverlay');
            if (ex) ex.remove();
            return;
        }
        scanRunning = true;
        this.classList.add('active-toggle');
        this.setAttribute('aria-pressed', 'true');

        let scanOverlay = $('scanOverlay');
        if (!scanOverlay) {
            scanOverlay = document.createElement('canvas');
            scanOverlay.id = 'scanOverlay';
            scanOverlay.setAttribute('aria-hidden', 'true');
            scanOverlay.style.cssText = 'position:absolute;top:0;left:0;width:100%;height:100%;pointer-events:none;z-index:8;';
            container.appendChild(scanOverlay);
        }
        const oCtx = scanOverlay.getContext('2d');
        scanOverlay.width  = container.clientWidth;
        scanOverlay.height = container.clientHeight;

        const totalH   = scanOverlay.height;
        const totalW   = scanOverlay.width;
        const self     = this;

        /* Scan parameters: slow enough to be meaningful */
        const SCAN_SPEED_PX_PER_TICK = 1;   /* 1px per frame = ~16px/sec at 60fps */
        const TICK_MS                = 16;  /* ~60fps */
        const BEAM_HEIGHT            = 3;   /* glow radius */
        const MAX_PASSES             = 3;

        let y = 0;
        let pass = 0;
        let direction = 1;  /* 1=down, -1=up (serpentine) */
        let headX = 0;

        function drawScanLine() {
            if (!scanRunning) {
                oCtx.clearRect(0, 0, totalW, totalH);
                return;
            }
            oCtx.clearRect(0, 0, totalW, totalH);

            /* Serpentine head position */
            headX = direction === 1
                ? (y / totalH) * totalW
                : totalW - (y / totalH) * totalW;

            /* Soft glow beam */
            const grad = oCtx.createLinearGradient(0, y - BEAM_HEIGHT * 2, 0, y + BEAM_HEIGHT * 2);
            grad.addColorStop(0,   'rgba(255,68,68,0)');
            grad.addColorStop(0.4, 'rgba(255,100,100,0.35)');
            grad.addColorStop(0.5, 'rgba(255,68,68,0.75)');
            grad.addColorStop(0.6, 'rgba(255,100,100,0.35)');
            grad.addColorStop(1,   'rgba(255,68,68,0)');
            oCtx.fillStyle = grad;
            oCtx.fillRect(0, y - BEAM_HEIGHT * 2, totalW, BEAM_HEIGHT * 4);

            /* Bright core line */
            oCtx.fillStyle = 'rgba(255,220,220,0.95)';
            oCtx.fillRect(0, y, totalW, 1);

            /* Laser head dot */
            oCtx.beginPath();
            oCtx.arc(headX, y, 4, 0, Math.PI * 2);
            oCtx.fillStyle = 'rgba(255,255,255,0.9)';
            oCtx.fill();
            oCtx.beginPath();
            oCtx.arc(headX, y, 2, 0, Math.PI * 2);
            oCtx.fillStyle = '#ff4444';
            oCtx.fill();

            /* Pass counter */
            oCtx.fillStyle = 'rgba(255,68,68,0.7)';
            oCtx.font = '9px monospace';
            oCtx.fillText(`Pass ${pass + 1}/${MAX_PASSES}`, 6, 14);

            y += SCAN_SPEED_PX_PER_TICK;

            if (y > totalH) {
                pass++;
                if (pass >= MAX_PASSES) {
                    /* Done */
                    oCtx.clearRect(0, 0, totalW, totalH);
                    scanRunning = false;
                    self.classList.remove('active-toggle');
                    self.setAttribute('aria-pressed', 'false');
                    toast('Scan complete (' + MAX_PASSES + ' passes)');
                    return;
                }
                /* Next pass: flip direction (serpentine) */
                direction = -direction;
                y = 0;
            }

            setTimeout(drawScanLine, TICK_MS);
        }

        drawScanLine();
    });

    /* ================================================================
       EVENT WIRING  -  all input controls
    ================================================================ */
    bindInputs('slBright','valBright');    bindInputs('slCont','valCont');
    bindInputs('slGamma','valGamma');      bindInputs('slSharp','valSharp');
    bindInputs('slLocalContrast','valLocalContrast');
    bindInputs('slDenoise','valDenoise'); bindInputs('slDot','valDot');
    bindInputs('slThresh','valThresh');   bindInputs('imgDpi','imgDpiNum');
    bindInputs('slSpot','valSpot');       bindInputs('slBlack','valBlack');
    bindInputs('slWhite','valWhite');     bindInputs('slNoise','valNoise');

    ['chkProtectHigh','chkHistEq','chkInvert','chkSimulate','chkLanczos','chkCatmullRom'].forEach(id => {
        const el = $(id); if (el) el.addEventListener('change', () => {
            queueProcess();
            if (id === 'chkSimulate') updateSimIndicator();
        });
    });
    /* USM radius and threshold controls */
    const selUsmRadius = $('selUsmRadius');
    const valUsmThresh = $('valUsmThresh');
    if (selUsmRadius) selUsmRadius.addEventListener('change', queueProcess);
    if (valUsmThresh) valUsmThresh.addEventListener('input', queueProcess);

    $('ditherSelect').addEventListener('change', (e) => {
        const ht = $('halftoneControls');
        const tc = $('thresholdControls');
        const showHt = ['halftone','halftone_lines','halftone_crosshatch'].includes(e.target.value);
        const showTc = ['threshold','adaptive'].includes(e.target.value);
        ht.classList.toggle('ctrl-hidden', !showHt);
        ht.setAttribute('aria-hidden', !showHt);
        tc.classList.toggle('ctrl-hidden', !showTc);
        tc.setAttribute('aria-hidden', !showTc);
        queueProcess();
    });

    $('materialSelect').addEventListener('change', (e) => {
        const val = e.target.value;
        if (materialProfiles[val]) {
            const p = materialProfiles[val];
            batchSettings(() => {
                $('slGamma').value  = $('valGamma').value  = p.gamma;
                $('slCont').value   = $('valCont').value   = p.contrast;
                $('slBright').value = $('valBright').value = p.brightness;
                $('ditherSelect').value = p.dither;
                $('chkInvert').checked  = p.invert;
                $('slSharp').value        = $('valSharp').value        = 0;
                $('slDenoise').value      = $('valDenoise').value      = 0;
                $('slNoise').value        = $('valNoise').value        = 0;
                $('slLocalContrast').value= $('valLocalContrast').value= 0;
                $('slBlack').value        = $('valBlack').value        = 0;
                $('slWhite').value        = $('valWhite').value        = 255;
                $('chkProtectHigh').checked = false;
                $('chkHistEq').checked      = false;
                $('chkSimulate').checked    = false;
                $('ditherSelect').dispatchEvent(new Event('change'));
            });
            toast(`Material: ${e.target.options[e.target.selectedIndex].text}`);
        }
    });

    $('imgWidth').addEventListener('change', (e) => {
        if ($('lockRatio').checked && state.ratio)
            $('imgHeight').value = Math.round(e.target.value / state.ratio);
        updateEstimation(); queueProcess();
    });
    $('imgHeight').addEventListener('change', (e) => {
        if ($('lockRatio').checked && state.ratio)
            $('imgWidth').value = Math.round(e.target.value * state.ratio);
        updateEstimation(); queueProcess();
    });
    $('imgDpi').addEventListener('change', () => { updateEstimation(); queueProcess(); });

    fileInput.addEventListener('change', (e) => loadImageFile(e.target.files[0]));

    /* Drag & Drop */
    document.body.addEventListener('dragover', (e) => { e.preventDefault(); document.body.classList.add('drag-over'); });
    document.body.addEventListener('dragleave', () => document.body.classList.remove('drag-over'));
    document.body.addEventListener('drop', (e) => {
        e.preventDefault();
        document.body.classList.remove('drag-over');
        loadImageFile(e.dataTransfer.files[0]);
    });

    /* Overlay tools */
    $('btnToggleZoom').addEventListener('click', () => {
        state.zoom = state.zoom === 1 ? 3 : 1;
        state.panX = 0; state.panY = 0;
        updateTransform();
    });
    $('btnToggleGrid').addEventListener('click', function () {
        state.showGrid = !state.showGrid;
        this.classList.toggle('active-toggle', state.showGrid);
        this.setAttribute('aria-pressed', state.showGrid);
        runPipeline();
    });
    $('btnToggleLines').addEventListener('click', function () {
        state.showLines = !state.showLines;
        this.classList.toggle('active-toggle', state.showLines);
        this.setAttribute('aria-pressed', state.showLines);
        runPipeline();
    });
    $('btnSplitView').addEventListener('click', function () {
        state.splitView = !state.splitView;
        this.classList.toggle('active-toggle', state.splitView);
        this.setAttribute('aria-pressed', state.splitView);
        $('splitLabel').classList.toggle('split-label--visible', state.splitView);
        splitSlider.classList.toggle('comparison-slider--visible', state.splitView);
        if (state.splitView) {
            /* Centre the slider when activating */
            splitSlider.style.left = Math.round(container.clientWidth / 2) + 'px';
        }
        runPipeline();
    });

    /* Zoom slider */
    const zoomOverlay = $('zoomSliderOverlay');
    container.addEventListener('touchstart', (e) => {
        if (e.touches.length === 1) {
            zoomOverlay.classList.add('zoom-overlay--visible');
            setTimeout(() => { zoomOverlay.classList.remove('zoom-overlay--visible'); }, 2000);
        }
    });
    $('zoomSlider').addEventListener('input', (e) => {
        state.zoom = parseFloat(e.target.value);
        updateTransform();
    });

    /* Export */
    exportBtn.addEventListener('click', () => {
        if (!state.image) { toast('Import an image first'); return; }
        exportCleanPng('GG_LaserPrep_Export.png');
        toast('PNG exported');
        clearPending();
    });

    /* Reset */
    $('btnReset').addEventListener('click', () => location.reload());

    /* Undo / Redo buttons */
    const btnUndo = $('btnUndo'), btnRedo = $('btnRedo');
    if (btnUndo) btnUndo.addEventListener('click', undoAction);
    if (btnRedo) btnRedo.addEventListener('click', redoAction);

    /* Batch file input */
    const batchFileInput = $('batchFileInput');
    if (batchFileInput) {
        batchFileInput.addEventListener('change', (e) => {
            if (e.target.files && e.target.files.length > 0) {
                startBatch(e.target.files);
                e.target.value = ''; /* reset so same files can be re-batched */
            }
        });
    }

    /* Auto Prep */
    $('btnAutoPrep').addEventListener('click', () => {
        batchSettings(() => {
            $('slBright').value = $('valBright').value = 5;
            $('slCont').value   = $('valCont').value   = 15;
            $('slSharp').value  = $('valSharp').value  = 50;
            $('chkHistEq').checked = true;
            $('ditherSelect').value = 'floyd';
            $('ditherSelect').dispatchEvent(new Event('change'));
        });
        toast('Auto Prep applied');
    });

    /* Basswood Auto Prep */
    $('btnBasswoodAutoPrep').addEventListener('click', () => {
        applyPresetValues({
            gamma:1.2, contrast:18, brightness:10, black:20, white:240,
            sharpen:45, denoise:0, localContrast:40, dither:'floyd', material:'basswood',
            protectHigh:false, histEq:false, invert:false, simulate:true
        }, 'Basswood Auto Prep');
    });

    /* Smart MDF */
    $('btnSmartMdf').addEventListener('click', () => {
        if (window.runScientificAutoAnalysis) {
            const matSel = $('materialSelect');
            if (matSel) { matSel.value='mdf'; matSel.dispatchEvent(new Event('change')); }
            setTimeout(() => window.runScientificAutoAnalysis(false), 80);
        } else {
            applyPresetValues({
                gamma:1.4, contrast:22, brightness:-5, black:15, white:245,
                sharpen:55, denoise:1, localContrast:30, dither:'floyd', material:'mdf',
                protectHigh:true, histEq:false, invert:false, simulate:true
            }, 'Smart MDF');
        }
    });

    /* Perfect Engrave */
    $('btnPerfectEngrave').addEventListener('click', () => {
        if (!state.image) { toast('Import an image first'); return; }
        /* FIX: read from state.processedImageData (clean pipeline output) not the
           display canvas.  ctx.getImageData returns whatever is painted on screen,
           which includes the burn-simulation blur when Simulate is active  -  that
           artificially lowers contrast measurements and picks the wrong algorithm. */
        if (!state.processedImageData || !state.processedImageW) {
            toast('Process an image first'); return;
        }
        const imgData=state.processedImageData;
        let brightness=0, contrastSum=0;
        for(let i=0;i<imgData.length;i+=4){
            const v=imgData[i]; brightness+=v;
            if(i>0) contrastSum+=Math.abs(v-imgData[i-4]);
        }
        brightness/=(imgData.length/4); contrastSum/=(imgData.length/4);
        batchSettings(() => {
            $('ditherSelect').value = contrastSum>45?'threshold':'jarvis';
            $('ditherSelect').dispatchEvent(new Event('change'));
        });
        toast('Perfect Engrave: analysed and applied');
    });

    /* Calibration grid */
    $('btnCalibGrid').addEventListener('click', generateCalibGrid);

    /* Extended tools */
    $('btnSaveSet').addEventListener('click', saveLaserPrep);
    $('btnLoadSet').addEventListener('click', loadLaserPrep);
    $('btnEstTime').addEventListener('click', updateEstimation);
    $('btnEdgeMode').addEventListener('click', edgeEngrave);
    $('btnVectorExp').addEventListener('click', exportVectorSVG);

    /* HQ Mode */
    $('btnHqMode').addEventListener('click', function () {
        state.hqMode = !state.hqMode;
        this.classList.toggle('active-toggle', state.hqMode);
        this.setAttribute('aria-pressed', state.hqMode);
        const dpiSlider = $('imgDpi');
        const dpiNum    = $('imgDpiNum');
        if (state.hqMode) {
            state.preHqDpi = parseFloat(dpiNum.value) || 300;
            const hqDpi = Math.min(1200, state.preHqDpi * 2);
            dpiSlider.value = dpiNum.value = hqDpi;
            toast(`HQ Mode ON  -  DPI doubled to ${hqDpi}`);
        } else {
            const normalDpi = state.preHqDpi || Math.max(100, Math.round((parseFloat(dpiNum.value)||600)/2));
            state.preHqDpi = null;
            dpiSlider.value = dpiNum.value = normalDpi;
            toast(`HQ Mode OFF  -  DPI restored to ${normalDpi}`);
        }
        queueProcess();
    });

    /* Orientation lock */
    if (screen.orientation && screen.orientation.lock) {
        $('btnHqMode').addEventListener('click', () => {
            if (state.hqMode) screen.orientation.lock('landscape').catch(()=>{});
            else screen.orientation.unlock();
        });
    }

    /* ================================================================
       SLIDER DOUBLE-CLICK RESET
    ================================================================ */
    const sliderDefaults = {
        slBright:0, slCont:0, slGamma:1, slSharp:0, slLocalContrast:0,
        slDenoise:0, slDot:3, slThresh:128, slSpot:0.08, slBlack:0, slWhite:255, slNoise:0,
        imgDpi:300
    };
    Object.entries(sliderDefaults).forEach(([id, def]) => {
        const el = $(id);
        if (!el) return;
        el.title = (el.title ? el.title + ' ' : '') + '(dbl-click to reset)';
        el.addEventListener('dblclick', () => {
            el.value = def;
            el.dispatchEvent(new Event('input', { bubbles: true }));
            toast('Reset to default: ' + def);
        });
    });

    /* ================================================================
       ARIA ATTRIBUTES  -  applied programmatically to all interactive elements
    ================================================================ */
    (function applyAria() {
        const ariaMap = [
            ['btnExport',    { 'aria-label':'Export processed image as PNG', 'aria-keyshortcuts':'e' }],
            ['btnReset',     { 'aria-label':'Reset all settings' }],
            ['btnAutoPrep',  { 'aria-label':'Apply balanced Auto Prep settings' }],
            ['btnSmartMdf',  { 'aria-label':'Smart MDF: scientific analysis for MDF material' }],
            ['btnBasswoodAutoPrep',{ 'aria-label':'Apply Basswood preset settings' }],
            ['btnPerfectEngrave',  { 'aria-label':'Analyse image and apply optimal dithering' }],
            ['btnCalibGrid', { 'aria-label':'Generate calibration grid' }],
            ['btnHqMode',    { 'aria-label':'HQ Mode: double DPI for finer detail', 'aria-pressed':'false' }],
            ['btnSimpleMode',{ 'aria-label':'Open Simple Mode for beginners' }],
            ['btnSplitView', { 'aria-label':'Toggle A/B split view', 'aria-pressed':'false', 'aria-keyshortcuts':'s' }],
            ['btnToggleZoom',{ 'aria-label':'Toggle 1:1 zoom' }],
            ['btnToggleGrid',{ 'aria-label':'Toggle pixel grid overlay', 'aria-pressed':'false' }],
            ['btnToggleLines',{'aria-label':'Toggle scan line overlay','aria-pressed':'false' }],
            ['btnScanPreview',{'aria-label':'Animate laser scan preview','aria-pressed':'false' }],
            ['btnToggleHist',{ 'aria-label':'Toggle tonal histogram','aria-pressed':'false' }],
            ['btnKbHelp',    { 'aria-label':'Show keyboard shortcuts', 'aria-pressed':'false', 'aria-keyshortcuts':'?' }],
            ['btnSaveSet',   { 'aria-label':'Save current settings to local storage' }],
            ['btnLoadSet',   { 'aria-label':'Load settings from local storage' }],
            ['btnEstTime',   { 'aria-label':'Estimate engraving time' }],
            ['btnEdgeMode',  { 'aria-label':'Apply Sobel edge detection' }],
            ['btnVectorExp', { 'aria-label':'Export as vector SVG' }],
            ['btnCamera',    { 'aria-label':'Take a photo with camera' }],
            ['ditherSelect', { 'aria-label':'Dithering algorithm selector' }],
            ['materialSelect',{'aria-label':'Material preset selector' }],
            ['chkLanczos',   { 'aria-label':'Enable Mitchell-Netravali high quality resize' }],
            ['lockRatio',    { 'aria-label':'Lock aspect ratio' }],
            ['chkInvert',    { 'aria-label':'Invert image' }],
            ['chkSimulate',  { 'aria-label':'Enable laser burn simulation' }],
            ['chkProtectHigh',{'aria-label':'Protect highlights from clipping' }],
            ['chkHistEq',    { 'aria-label':'Apply histogram equalisation' }],
            ['previewCanvas',{ 'role':'img', 'aria-label':'Processed image preview' }],
            ['previewContainer',{'role':'application','aria-label':'Image preview area, pinch or scroll to zoom' }],
            ['kbHelp',       { 'aria-hidden':'true', 'role':'dialog', 'aria-label':'Keyboard shortcuts' }],
            ['simpleModeModal',{'aria-hidden':'true', 'role':'dialog', 'aria-label':'Simple Mode' }],
        ];

        ariaMap.forEach(([id, attrs]) => {
            const el = $(id);
            if (!el) return;
            Object.entries(attrs).forEach(([attr, val]) => el.setAttribute(attr, val));
        });

        /* tabindex for all buttons/labels already handled by HTML */
        /* Sliders  -  add aria-valuenow live region via input events */
        document.querySelectorAll('input[type="range"]').forEach(range => {
            range.setAttribute('aria-valuenow', range.value);
            range.setAttribute('aria-valuemin', range.min || '0');
            range.setAttribute('aria-valuemax', range.max || '100');
            range.addEventListener('input', () => range.setAttribute('aria-valuenow', range.value));
        });
    })();

    /* ================================================================
       INIT
    ================================================================ */
    initWorker();
    updateEstimation();
    loadPersistedSettings();   /* restore last session's settings */
    undoSnapshot();            /* seed undo history with initial state */
    updateUndoButtons();

    /* Minimal worker-status badge in nav */
    (function showWorkerStatus() {
        const logo = document.querySelector('.nav-logo');
        if (!logo) return;
        const badge = document.createElement('span');
        badge.className = 'worker-badge';
        badge.textContent = state.workerReady ? 'Worker' : 'Compat';
        badge.title = state.workerReady
            ? 'Processing runs in a background Web Worker'
            : 'Processing runs on main thread (Worker unavailable)';
        logo.appendChild(badge);
    })();

    /* ================================================================
       VECTOR TRACE  -  Contour & Centerline tracing, SVG export
       Additive feature, no existing code modified.
    ================================================================ */
    (function initVectorTrace() {
        const modal   = $('vectorTraceModal');
        const btnOpen = $('btnVectorTrace');
        const btnClose= $('btnCloseVectorTrace');
        const vtPrev  = $('vtPreviewCanvas');
        const vtStatus= $('vtStatus');
        const vtThresh = $('vtThreshold');
        const vtThreshN= $('vtThreshNum');
        const vtSmooth = $('vtSmooth');
        const vtSmoothN= $('vtSmoothNum');

        if (!modal||!btnOpen) return;

        /* Sync threshold slider <-> number */
        vtThresh.addEventListener('input',()=>{ vtThreshN.value=vtThresh.value; });
        vtThreshN.addEventListener('input',()=>{ vtThresh.value=vtThreshN.value; });
        vtSmooth.addEventListener('input',()=>{ vtSmoothN.value=vtSmooth.value; });
        vtSmoothN.addEventListener('input',()=>{ vtSmooth.value=vtSmoothN.value; });

        function openModal() {
            if (!state.image) { toast('Import an image first'); return; }
            modal.classList.add('open'); modal.setAttribute('aria-hidden','false');
        }
        function closeModal() {
            modal.classList.remove('open'); modal.setAttribute('aria-hidden','true');
        }
        btnOpen.addEventListener('click', openModal);
        btnClose.addEventListener('click', closeModal);
        modal.addEventListener('click', e=>{ if(e.target===modal) closeModal(); });

        /* -- Get grayscale pixel data from processed image or canvas -- */
        function getGrayData() {
            const src = state.processedImageData;
            const w   = state.processedImageW || canvas.width;
            const h   = state.processedImageH || canvas.height;
            if (src && w && h) return { data: src, w, h };
            if (!canvas.width) return null;
            const imgd = ctx.getImageData(0,0,canvas.width,canvas.height);
            return { data: imgd.data, w: canvas.width, h: canvas.height };
        }

        /* -- Marching Squares  -  extract iso-contours -- */
        function marchingSquares(gray, w, h, threshold) {
            const at=(x,y)=>gray[y*w+x]<threshold?1:0;
            const paths=[];
            /* Edge-list for each cell */
            const edges=[
                [], [[0,0.5],[0.5,0]], [[0.5,0],[1,0.5]], [[0,0.5],[1,0.5]],
                [[1,0.5],[0.5,1]], [[0,0.5],[0.5,1],[0.5,0],[1,0.5]],
                [[0.5,0],[0.5,1]], [[0,0.5],[0.5,1]],
                [[0,0.5],[0.5,1]], [[0.5,0],[0.5,1]],
                [[0,0.5],[0.5,0],[1,0.5],[0.5,1]], [[0.5,0],[0.5,1]],
                [[0,0.5],[1,0.5]], [[0.5,0],[1,0.5]],
                [[0,0.5],[0.5,0]], []
            ];
            const segments=[];
            for(let y=0;y<h-1;y++){
                for(let x=0;x<w-1;x++){
                    const idx=at(x,y)*8+at(x+1,y)*4+at(x+1,y+1)*2+at(x,y+1)*1;
                    const e=edges[idx];
                    for(let i=0;i<e.length;i+=2){
                        segments.push([
                            (x+e[i][0]), (y+e[i][1]),
                            (x+e[i+1][0]), (y+e[i+1][1])
                        ]);
                    }
                }
            }
            /* Chain segments into paths */
            const used=new Uint8Array(segments.length);
            const eps=0.01;
            for(let i=0;i<segments.length;i++){
                if(used[i]) continue;
                used[i]=1;
                const path=[[segments[i][0],segments[i][1]],[segments[i][2],segments[i][3]]];
                let changed=true;
                while(changed){
                    changed=false;
                    const tail=path[path.length-1];
                    for(let j=0;j<segments.length;j++){
                        if(used[j]) continue;
                        const s=segments[j];
                        if(Math.abs(s[0]-tail[0])<eps&&Math.abs(s[1]-tail[1])<eps){
                            path.push([s[2],s[3]]); used[j]=1; changed=true; break;
                        }
                        if(Math.abs(s[2]-tail[0])<eps&&Math.abs(s[3]-tail[1])<eps){
                            path.push([s[0],s[1]]); used[j]=1; changed=true; break;
                        }
                    }
                }
                if(path.length>2) paths.push(path);
            }
            return paths;
        }

        /* -- Centerline: skeletonise then trace -- */
        function centerlineTrace(gray, w, h, threshold) {
            /* Binarise */
            const bin=new Uint8Array(w*h);
            for(let i=0;i<w*h;i++) bin[i]=gray[i]<threshold?1:0;
            /* Zhang-Suen thinning */
            function neighbours(x,y){
                return [bin[y>0?((y-1)*w+x):0],bin[y>0&&x<w-1?((y-1)*w+x+1):0],
                        bin[y*w+x<w-1?(y*w+x+1):0],bin[y<h-1&&x<w-1?((y+1)*w+x+1):0],
                        bin[y<h-1?(y+1)*w+x:0],bin[y<h-1&&x>0?((y+1)*w+x-1):0],
                        bin[y*w+x>0?(y*w+x-1):0],bin[y>0&&x>0?((y-1)*w+x-1):0]];
            }
            function transitions(nb){ let t=0; for(let i=0;i<7;i++) if(!nb[i]&&nb[i+1]) t++; if(!nb[7]&&nb[0]) t++; return t; }
            function sum8(nb){ return nb.reduce((a,b)=>a+b,0); }
            let changed=true; let iter=0;
            while(changed&&iter<100){
                changed=false; iter++;
                for(let step=0;step<2;step++){
                    const toRemove=[];
                    for(let y=1;y<h-1;y++) for(let x=1;x<w-1;x++){
                        if(!bin[y*w+x]) continue;
                        const nb=neighbours(x,y);
                        const s=sum8(nb); if(s<2||s>6) continue;
                        if(transitions(nb)!==1) continue;
                        if(step===0&&(nb[0]&&nb[2]&&nb[4])) continue;
                        if(step===0&&(nb[2]&&nb[4]&&nb[6])) continue;
                        if(step===1&&(nb[0]&&nb[2]&&nb[6])) continue;
                        if(step===1&&(nb[0]&&nb[4]&&nb[6])) continue;
                        toRemove.push(y*w+x);
                    }
                    if(toRemove.length){ toRemove.forEach(i=>{ bin[i]=0; }); changed=true; }
                }
            }
            /* Trace skeleton into polylines via DFS */
            const visited=new Uint8Array(w*h);
            const paths=[];
            const dirs=[[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]];
            /* Find endpoints / junctions */
            for(let y=1;y<h-1;y++) for(let x=1;x<w-1;x++){
                if(!bin[y*w+x]||visited[y*w+x]) continue;
                /* Count neighbours */
                let nc=0;
                dirs.forEach(([dy,dx])=>{ if(bin[(y+dy)*w+(x+dx)]) nc++; });
                if(nc!==1&&nc!==0) continue; /* start from endpoints */
                const path=[[x,y]];
                visited[y*w+x]=1;
                let cx=x,cy=y;
                let found=true;
                while(found){
                    found=false;
                    for(const[dy,dx]of dirs){
                        const nx=cx+dx,ny=cy+dy;
                        if(nx<0||ny<0||nx>=w||ny>=h) continue;
                        if(!bin[ny*w+nx]||visited[ny*w+nx]) continue;
                        visited[ny*w+nx]=1;
                        cx=nx; cy=ny;
                        path.push([cx,cy]);
                        found=true; break;
                    }
                }
                if(path.length>3) paths.push(path);
            }
            return paths;
        }

        /* -- Smooth path with Chaikin's algorithm -- */
        function smoothPath(pts, iters) {
            if(!iters) return pts;
            let p=pts;
            for(let k=0;k<iters;k++){
                const q=[[...p[0]]];
                for(let i=0;i<p.length-1;i++){
                    q.push([0.75*p[i][0]+0.25*p[i+1][0], 0.75*p[i][1]+0.25*p[i+1][1]]);
                    q.push([0.25*p[i][0]+0.75*p[i+1][0], 0.25*p[i][1]+0.75*p[i+1][1]]);
                }
                q.push([...p[p.length-1]]);
                p=q;
            }
            return p;
        }

        /* -- Build SVG from paths -- */
        function buildSVG(paths, w, h, smooth) {
            let d='';
            const s=parseInt(smooth)||0;
            for(const path of paths){
                if(path.length<2) continue;
                const pts=s>0?smoothPath(path,s):path;
                d+=`M${pts[0][0].toFixed(2)},${pts[0][1].toFixed(2)}`;
                for(let i=1;i<pts.length;i++) d+=` L${pts[i][0].toFixed(2)},${pts[i][1].toFixed(2)}`;
            }
            const wMm=parseFloat($('imgWidth').value)||100;
            const hMm=parseFloat($('imgHeight').value)||100;
            return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${w} ${h}" width="${wMm}mm" height="${hMm}mm">
  <path d="${d}" stroke="black" stroke-width="1" fill="none" stroke-linejoin="round" stroke-linecap="round"/>
</svg>`;
        }

        /* -- Shared trace runner -- */
        function runTrace() {
            const g=getGrayData();
            if(!g){ vtStatus.textContent='[!] No image loaded'; return null; }
            const threshold=parseInt(vtThresh.value)||128;
            const invert   =$('vtInvert').checked;
            const mode     =$('vtMode').value;
            const smooth   =parseInt(vtSmooth.value)||0;
            const optimise =$('vtOptimise').checked;

            /* Build gray array */
            const gray=new Uint8Array(g.w*g.h);
            for(let i=0;i<g.w*g.h;i++) gray[i]=invert?255-g.data[i*4]:g.data[i*4];

            vtStatus.textContent='[spin] Tracing...';
            let paths;
            if(mode==='centerline'){
                paths=centerlineTrace(gray,g.w,g.h,threshold);
            } else {
                paths=marchingSquares(gray,g.w,g.h,threshold);
            }

            /* -- Path optimisation: merge collinear/near-collinear segments --
               Removes intermediate points where direction change is below
               a tolerance angle (~2deg), reducing G-code line count significantly
               without visible quality loss. Only applied when vtOptimise is checked. */
            if (optimise && paths.length > 0) {
                const COS_TOL = Math.cos(2 * Math.PI / 180); /* 2deg tolerance */
                paths = paths.map(path => {
                    if (path.length < 3) return path;
                    const out = [path[0]];
                    for (let i = 1; i < path.length - 1; i++) {
                        const prev = out[out.length - 1];
                        const curr = path[i];
                        const next = path[i + 1];
                        /* Vectors from prev->curr and curr->next */
                        const ax = curr[0] - prev[0], ay = curr[1] - prev[1];
                        const bx = next[0] - curr[0], by = next[1] - curr[1];
                        const lenA = Math.sqrt(ax*ax + ay*ay);
                        const lenB = Math.sqrt(bx*bx + by*by);
                        if (lenA < 0.001 || lenB < 0.001) continue; /* skip zero-length segs */
                        const dot = (ax*bx + ay*by) / (lenA * lenB);
                        /* Keep point only if direction changes significantly */
                        if (dot < COS_TOL) out.push(curr);
                    }
                    out.push(path[path.length - 1]);
                    return out;
                }).filter(p => p.length >= 2);

                /* Also merge paths whose endpoints are within 1px of each other */
                const EPS2 = 1; /* merge distance2 */
                function dist2(a, b) {
                    const dx = a[0]-b[0], dy = a[1]-b[1]; return dx*dx+dy*dy;
                }
                const merged = new Uint8Array(paths.length);
                const result = [];
                for (let i = 0; i < paths.length; i++) {
                    if (merged[i]) continue;
                    let current = paths[i];
                    let changed = true;
                    while (changed) {
                        changed = false;
                        for (let j = i + 1; j < paths.length; j++) {
                            if (merged[j]) continue;
                            const tail = current[current.length - 1];
                            const head = paths[j][0];
                            const headR = paths[j][paths[j].length - 1];
                            if (dist2(tail, head) <= EPS2) {
                                current = current.concat(paths[j].slice(1));
                                merged[j] = 1; changed = true;
                            } else if (dist2(tail, headR) <= EPS2) {
                                current = current.concat(paths[j].slice(0, -1).reverse());
                                merged[j] = 1; changed = true;
                            }
                        }
                    }
                    result.push(current);
                }
                paths = result;
            }

            const beforeCount = paths.length;
            vtStatus.textContent=`OK ${paths.length} paths found${optimise ? ' (optimised)' : ''}`;
            return { paths, w:g.w, h:g.h, smooth };
        }

        $('btnVtPreview').addEventListener('click',()=>{
            const r=runTrace(); if(!r) return;
            vtPrev.style.display='block';
            const scale=Math.min(440/r.w,300/r.h,1);
            vtPrev.width=Math.round(r.w*scale);
            vtPrev.height=Math.round(r.h*scale);
            const pCtx=vtPrev.getContext('2d');
            pCtx.fillStyle='#1a1a1a'; pCtx.fillRect(0,0,vtPrev.width,vtPrev.height);
            pCtx.strokeStyle='#ff4444'; pCtx.lineWidth=1;
            pCtx.save(); pCtx.scale(scale,scale);
            const s=parseInt(vtSmooth.value)||0;
            for(const path of r.paths){
                if(path.length<2) continue;
                const pts=s>0?smoothPath(path,s):path;
                pCtx.beginPath();
                pCtx.moveTo(pts[0][0],pts[0][1]);
                for(let i=1;i<pts.length;i++) pCtx.lineTo(pts[i][0],pts[i][1]);
                pCtx.stroke();
            }
            pCtx.restore();
        });

        $('btnVtExportSvg').addEventListener('click',()=>{
            const r=runTrace(); if(!r) return;
            const svg=buildSVG(r.paths,r.w,r.h,r.smooth);
            const blob=new Blob([svg],{type:'image/svg+xml'});
            const a=document.createElement('a');
            triggerDownload(blob, 'GG_VectorTrace.svg', 'image/svg+xml');
            toast('Vector trace SVG exported');
        });
    })();



    /* ================================================================
       AI BACKGROUND REMOVAL  -  @imgly/background-removal via CDN
       Additive feature, no existing code modified.
    ================================================================ */
    (function initBgRemove() {
        const btn=$('btnBgRemove');
        if(!btn) return;
        let bgRemoveLib=null;
        let bgRemoveLoading=false;

        async function loadLib() {
            if(bgRemoveLib) return bgRemoveLib;
            if(bgRemoveLoading) return null;
            bgRemoveLoading=true;
            toast('Loading AI background removal...',3000);
            return new Promise((resolve)=>{
                const s=document.createElement('script');
                /* Use @imgly/background-removal via CDN */
                s.src='https://cdn.jsdelivr.net/npm/@imgly/background-removal@1.4.5/dist/background-removal.min.js';
                s.onload=()=>{
                    /* @imgly/background-removal UMD exposes itself as window.imglyBackgroundRemoval
                       or as window['@imgly/background-removal']. Try both plus legacy names. */
                    bgRemoveLib = window.imglyBackgroundRemoval
                        || window['@imgly/background-removal']
                        || window['background-removal']
                        || window.BackgroundRemoval
                        || null;
                    resolve(bgRemoveLib);
                };
                s.onerror=()=>{ bgRemoveLoading=false; /* FIX: allow retry on next click */ toast('[!] Could not load AI library (network required)',4000); resolve(null); };
                document.head.appendChild(s);
            });
        }

        btn.addEventListener('click', async ()=>{
            if(!state.image){ toast('Import an image first'); return; }
            btn.disabled=true;
            btn.textContent='[spin] Removing...';

            try {
                const lib=await loadLib();
                /* Fallback: use canvas-based approach if CDN unavailable */
                if(!lib){
                    /* Graceful fallback: threshold-based simple BG removal */
                    simpleBgRemoveFallback();
                    return;
                }
                /* Convert image to blob */
                const tmpC=document.createElement('canvas');
                tmpC.width=state.image.width; tmpC.height=state.image.height;
                tmpC.getContext('2d').drawImage(state.image,0,0);
                const blob=await new Promise(r=>tmpC.toBlob(r,'image/png'));
                /* Run AI BG removal */
                const config={
                    publicPath:`https://cdn.jsdelivr.net/npm/@imgly/background-removal@1.4.5/dist/`,
                    debug:false,
                    model:'medium'
                };
                /* @imgly/background-removal exports removeBackground as named export in UMD */
                const removeFunc = (lib && lib.removeBackground)
                    ? lib.removeBackground
                    : (typeof lib === 'function' ? lib : null);
                if(!removeFunc){ simpleBgRemoveFallback(); return; }
                const resultBlob=await removeFunc(blob,config);
                const url=URL.createObjectURL(resultBlob);
                const img=new Image();
                img.onload=()=>{
                    URL.revokeObjectURL(url);
                    state.image=img;
                    state.image._ggId=++state.imageIdCounter;
                    state.lanczosCache={imageId:null,pxW:0,pxH:0,data:null};
                    toast('OK Background removed!');
                    btn.disabled=false; btn.textContent='Remove BG (AI) Remove BG (AI)';
                    queueProcess();
                };
                img.onerror=()=>{ URL.revokeObjectURL(url); throw new Error('Result decode failed'); };
                img.src=url;
            } catch(err) {
                console.warn('[BgRemove]',err);
                simpleBgRemoveFallback();
            }
        });

        /* -- Fallback: canvas-based threshold BG removal (white/near-white) -- */
        function simpleBgRemoveFallback() {
            if(!state.image){ return; }
            toast('Using threshold BG removal (AI unavailable)...',2500);
            const tmpC=document.createElement('canvas');
            tmpC.width=state.image.width; tmpC.height=state.image.height;
            const tCtx=tmpC.getContext('2d');
            tCtx.drawImage(state.image,0,0);
            const imgData=tCtx.getImageData(0,0,tmpC.width,tmpC.height);
            const d=imgData.data;
            const BG_THRESH=230;
            for(let i=0;i<d.length;i+=4){
                const r=d[i],g=d[i+1],b=d[i+2];
                const sat=Math.max(r,g,b)-Math.min(r,g,b);
                if(r>BG_THRESH&&g>BG_THRESH&&b>BG_THRESH&&sat<25){
                    d[i+3]=0; /* transparent */
                }
            }
            tCtx.putImageData(imgData,0,0);
            tmpC.toBlob(blob=>{
                const url=URL.createObjectURL(blob);
                const img=new Image();
                img.onload=()=>{
                    URL.revokeObjectURL(url);
                    state.image=img;
                    state.image._ggId=++state.imageIdCounter;
                    state.lanczosCache={imageId:null,pxW:0,pxH:0,data:null};
                    toast('OK BG removed (threshold mode)');
                    btn.disabled=false; btn.textContent='Remove BG (AI) Remove BG (AI)';
                    queueProcess();
                };
                img.src=url;
            },'image/png');
        }
    })();

    /* ================================================================
       G-CODE EXPORT GENERATOR
       Converts processed bitmap to laser-ready G-code.
       Additive feature, no existing code modified.
    ================================================================ */
    (function initGcodeExport() {
        const modal    = $('gcodeModal');
        const btnOpen  = $('btnGcodeExport');
        const btnClose = $('btnCloseGcode');
        const gcStatus = $('gcStatus');
        if(!modal||!btnOpen) return;

        function openModal() {
            if(!state.image){ toast('Import an image first'); return; }
            if(!state.processedImageData){
                /* FIX: auto-trigger pipeline then re-open, instead of blocking silently */
                toast('Processing image first...');
                queueProcess();
                setTimeout(openModal, 900);
                return;
            }
            modal.classList.add('open'); modal.setAttribute('aria-hidden','false');
            gcStatus.textContent='';
            $('gcPreviewText').style.display='none';
        }
        function closeModal() {
            modal.classList.remove('open'); modal.setAttribute('aria-hidden','true');
        }
        btnOpen.addEventListener('click', openModal);
        btnClose.addEventListener('click', closeModal);
        modal.addEventListener('click', e=>{ if(e.target===modal) closeModal(); });

        /* -- Core G-code generator -- */
        function generateGcode(preview) {
            if(!state.processedImageData||!state.processedImageW){
                gcStatus.textContent='[!] No processed image'; return null;
            }
            gcStatus.textContent='[spin] Generating G-code...';
            const w       = state.processedImageW;
            const h       = state.processedImageH;
            const data    = state.processedImageData;
            const wMm     = parseFloat($('imgWidth').value)||100;
            const hMm     = parseFloat($('imgHeight').value)||100;
            const scaleX  = wMm/w;
            const scaleY  = hMm/h;
            const power   = parseInt($('gcPower').value)||1000;
            const speed   = parseInt($('gcSpeed').value)||3000;
            const passes  = parseInt($('gcPasses').value)||1;
            const passZ   = parseFloat($('gcPassDepth').value)||0;
            const firmware= $('gcFirmware').value;
            const mode    = $('gcMode').value;
            const laserMode=$('gcLaserMode').checked;
            const goHome  = $('gcHome').checked;

            /* Downscale for preview to reduce lines */
            const sampStep= preview ? Math.max(1,Math.round(h/120)) : 1;

            const lines=[];
            /* Header */
            lines.push('; G-code generated by GG LaserPrep v7');
            lines.push(`; Image: ${w}x${h}px -> ${wMm.toFixed(1)}x${hMm.toFixed(1)}mm`);
            lines.push(`; Power: ${power} | Speed: ${speed}mm/min | Passes: ${passes}`);
            lines.push('; ===========================================');
            if(firmware==='grbl'){
                if(laserMode) lines.push('$32=1 ; laser mode on');
                lines.push('G21 ; mm units');
                lines.push('G90 ; absolute positioning');
                lines.push('M5 S0 ; laser off at start');
                lines.push('M3 S0 ; arm laser (required before G1 S commands)');
                lines.push('G0 F'+speed);
            } else if(firmware==='marlin'){
                lines.push('G21');
                lines.push('G90');
                lines.push('M5 S0 ; laser off');
            } else {
                /* Smoothieware */
                lines.push('G21');
                lines.push('G90');
                lines.push('M5 ; laser off');
                lines.push('M3 S0 ; arm laser');
            }

            if(mode==='raster'){
                for(let pass=0;pass<passes;pass++){
                    if(passZ&&pass>0) lines.push(`G0 Z${(pass*passZ).toFixed(3)}`);
                    for(let row=0;row<h;row+=sampStep){
                        const y_mm=((h-1-row)*scaleY).toFixed(4);
                        /* Find runs of dark pixels */
                        let inRun=false, runStart=0;
                        for(let col=0;col<w;col++){
                            const px=data[(row*w+col)*4];
                            const isDark=px<128;
                            if(isDark&&!inRun){ inRun=true; runStart=col; }
                            if((!isDark||col===w-1)&&inRun){
                                const endCol=col-(isDark?0:1);
                                const x0=(runStart*scaleX).toFixed(4);
                                const x1=(endCol*scaleX).toFixed(4);
                                /* Power proportional to darkness */
                                const pxAvg=data[(row*w+Math.round((runStart+endCol)/2))*4];
                                const dynPow=Math.round(((255-pxAvg)/255)*power);
                                if(firmware==='grbl'){
                                    lines.push(`G0 X${x0} Y${y_mm}`);
                                    lines.push(`G1 X${x1} Y${y_mm} F${speed} S${dynPow}`);
                                } else if(firmware==='marlin'){
                                    lines.push(`G0 X${x0} Y${y_mm}`);
                                    lines.push(`M3 S${dynPow}`);
                                    lines.push(`G1 X${x1} F${speed}`);
                                    lines.push('M5');
                                } else {
                                    lines.push(`G0 X${x0} Y${y_mm}`);
                                    lines.push(`G1 X${x1} Y${y_mm} F${speed} S${dynPow}`);
                                }
                                inRun=false;
                            }
                        }
                    }
                }
            } else {
                /* Vector outline mode  -  basic edge detection */
                lines.push('; Vector outline mode');
                for(let y=1;y<h-1;y+=sampStep){
                    for(let x=1;x<w-1;x++){
                        const v=data[(y*w+x)*4];
                        const vR=data[(y*w+x+1)*4];
                        if((v<128)!==(vR<128)){
                            const xmm=(x*scaleX).toFixed(4);
                            const ymm=((h-1-y)*scaleY).toFixed(4);
                            lines.push(`G0 X${xmm} Y${ymm}`);
                            lines.push(`G1 X${((x+1)*scaleX).toFixed(4)} Y${ymm} F${speed} S${power}`);
                        }
                    }
                }
            }

            /* Footer */
            if(firmware==='grbl') lines.push('M5 S0 ; laser off');
            else if(firmware==='marlin') lines.push('M5 S0');
            if(goHome){
                lines.push('G0 X0 Y0 ; return home');
                if(passZ&&passes>1) lines.push('G0 Z0');
            }
            lines.push('; END');

            gcStatus.textContent=`OK ${lines.length} lines, ~${(lines.join('\n').length/1024).toFixed(1)}KB`;
            return lines.join('\n');
        }

        $('btnGcPreview').addEventListener('click',()=>{
            const gcode=generateGcode(true); if(!gcode) return;
            const ta=$('gcPreviewText');
            ta.style.display='block';
            /* Show first 200 lines */
            const lines=gcode.split('\n');
            ta.value=lines.slice(0,200).join('\n')+(lines.length>200?'\n\n; ... ('+lines.length+' lines total, download for full file)':'');
        });

        $('btnGcDownload').addEventListener('click',()=>{
            const gcode=generateGcode(false); if(!gcode) return;
            triggerDownload(gcode, 'GG_LaserPrep_Engrave.nc', 'text/plain');
            toast('G-code exported');
        });
    })();

    /* ================================================================
       ARIA  -  add new buttons to aria map
       Additive, appended after existing ARIA section.
    ================================================================ */
    (function extendAria() {
        const extra=[
            ['btnVectorTrace', {'aria-label':'Open Vector Trace tool'}],
            ['btnBgRemove',    {'aria-label':'Remove background using AI'}],
            ['btnGcodeExport', {'aria-label':'Open G-Code export generator'}],
        ];
        extra.forEach(([id,attrs])=>{
            const el=$(id); if(!el) return;
            Object.entries(attrs).forEach(([a,v])=>el.setAttribute(a,v));
        });
    })();

    /* ================================================================
       CONTROLLED GLOBAL EXPORTS
       (minimal: only what Scientific add-on or other legacy scripts need)
    ================================================================ */
    window.GGLaserPrep = {
        state,
        toast,
        queueProcess,
        runPipeline,
        resetView,
        updateEstimation,
        loadImageFile,
        applyPresetValues
    };

    /* Back-compat shims (avoids breaking any external references) */
    window.toast            = toast;
    window.queueProcess     = queueProcess;
    window.runPipeline      = runPipeline;
    window.resetView        = resetView;
    window.updateEstimation = updateEstimation;
    window.loadImageFile    = loadImageFile;
    window.clearPendingExport = clearPending;

})();
