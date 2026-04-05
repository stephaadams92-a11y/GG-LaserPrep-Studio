const CACHE_NAME = 'grainglow-cache-v2';
const FILES_TO_CACHE = [
    './index.html',
    './laserprep.css',
    './laserprep.js',
    './manifest.json',
    './icon-192.png',
    './icon-512.png'
    /* laserprep-worker.js removed: worker is now inlined as a Blob URL in laserprep.js
       and is never fetched as a separate file. Including it here would cause
       cache.addAll() to fail if the file is absent, breaking SW install entirely. */
];

// Install the service worker and cache all core files
self.addEventListener('install', (event) => {
    event.waitUntil(
        caches.open(CACHE_NAME).then((cache) => {
            console.log('[ServiceWorker] Pre-caching offline page');
            return cache.addAll(FILES_TO_CACHE);
        })
    );
    self.skipWaiting();
});

// Clean up old caches when a new version activates
self.addEventListener('activate', (event) => {
    event.waitUntil(
        caches.keys().then((keyList) => {
            return Promise.all(keyList.map((key) => {
                if (key !== CACHE_NAME) {
                    console.log('[ServiceWorker] Removing old cache', key);
                    return caches.delete(key);
                }
            }));
        })
    );
    self.clients.claim();
});

// Intercept network requests and serve from cache if available
self.addEventListener('fetch', (event) => {
    event.respondWith(
        caches.match(event.request).then((response) => {
            return response || fetch(event.request);
        })
    );
});