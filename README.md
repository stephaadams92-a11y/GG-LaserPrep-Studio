# G&G LaserPrep Pro Studio
Professional image preparation tool for laser engraving — free, no install needed.
Built by Stephanie Adams, Stoke-on-Trent, for G&G LaserPrep Studio.
Use it now
Open the app
Works on any phone, tablet or computer. No account, no download, no login. Just tap the link and go.
How to use it — 4 steps
Import — tap + Import and choose your image
Size — set the width and height in mm to match your material
Material — pick your material from the dropdown. The app sets everything else automatically
Export PNG — tap the red Export button at the bottom
That is all you need for great results. The advanced sliders are optional fine-tuning.
Preset buttons
Button
What it does
⚡ Simple
Step-by-step guided mode for beginners
Auto Prep
Balanced general-purpose preset, good for most images
Smart MDF ⚡
Analyses the image and optimises settings specifically for MDF
🪵 Basswood
Tuned for pale basswood ply — lifts shadows, boosts local contrast
Perfect Engrave
Reads the processed image and picks the best dithering algorithm automatically
HQ Mode
Doubles DPI for finer detail on small engravings
Calib Grid
Generates a calibration test grid for your laser
Materials supported
Bamboo, Basswood ply, MDF, Leather, Canvas, Glass, Acrylic, Anodised aluminium, Black painted ceramic tile, White painted ceramic tile, Rainbow scratch paper, Slate, Granite
Each material has individually calibrated gamma, contrast, brightness and dithering settings based on how that material responds to laser engraving.
How it works — the science
Every image is processed through a scientifically correct pipeline:
Mitchell-Netravali bicubic resampling — the same algorithm used by professional print software. Preserves fine detail when scaling to your engraving dimensions
Rec.709 greyscale conversion — the broadcast TV luminance standard. Weights red, green and blue channels correctly for human perception rather than averaging them equally
Tonal pipeline — contrast, brightness, gamma and black/white point applied in the correct scientific order to preserve shadow and highlight detail
Error-diffusion dithering — Floyd-Steinberg, Jarvis-Judice-Ninke, Stucki, Atkinson, Riemersma (Hilbert curve), plus Bayer ordered dithering at 2×2, 4×4 and 8×8. Converts greyscale to pure black/white while preserving the appearance of gradients
pHYs DPI metadata — the exported PNG has physical dimensions embedded so your laser controller knows the exact size without manual entry
Processing runs entirely in your browser using a Web Worker — nothing is uploaded to any server. Your images stay on your device.
Processing time
Most images: 5–15 seconds. Large images at high DPI with error-diffusion dithering can take up to 60 seconds. The spinning circle and progress bar confirm the app is working — do not close it while processing.
Advanced features
A/B split view — drag the divider to compare original and processed side by side
Batch processing — import multiple images and export them all with the same settings
Vector trace — trace the processed image to SVG paths (contour or centerline)
Crop & Rotate — interactive crop with draggable handles, flip and rotate tools
G-Code export — generate GRBL/LightBurn/Marlin compatible G-code directly
AI background removal — remove backgrounds before processing
Undo/Redo — 20-step history, also Ctrl+Z / Ctrl+Y on desktop
Laser simulation — preview how the engraving will look on the material
Histogram overlay — live tonal histogram for precise adjustments
Settings persistence — your settings are automatically saved and restored
Android app
An Android APK is available for offline use. Download it from the Releases page and install directly — no Play Store needed. Enable "Install from unknown sources" in your Android settings when prompted.
Tips
Change one setting at a time. The image re-processes automatically after every change — if you move several sliders at once you will not know which one made the difference
Double-tap any slider to reset it to its default value
The material preset resets all sliders to a clean baseline — apply it first, then tweak if needed
For portraits and photos, Smart MDF or Auto Prep with Floyd-Steinberg dithering gives the best results
For logos and line art, try Threshold dithering with Catmull-Rom mode enabled
Credits
Created by Stephanie Adams for G&G LaserPrep Studio, Stoke-on-Trent, UK.
© 2026 Stephanie Adams. All Rights Reserved.
This software is the intellectual property of Stephanie Adams. Unauthorised copying, redistribution or claiming of this work as your own is strictly prohibited.
