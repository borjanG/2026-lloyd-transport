# Vortex mesh animations

The 31 × 31-generator vortex calculation used in Figure 1, from simulation time
`t = 0` to `t = 1`, without and with Lloyd stabilization.

| Unstabilized | Stabilized |
| --- | --- |
| [![Unstabilized mesh](vortex-unstabilized.gif)](../vortex-unstabilized.mp4) | [![Stabilized mesh](vortex-stabilized.gif)](../vortex-stabilized.mp4) |

The full-resolution MP4s are at the repository root. Each is 1080 × 1080,
30 fps, and 301 frames (about ten seconds), encoded as H.264 with `yuv420p`
and fast-start metadata. The looping GIF previews are 420 × 420 at 20 fps.
The `*-end.png` files are still previews of the final states.

The original solver settings and adaptive time steps are preserved. Each
accepted particle configuration is recorded. For smooth, synchronized playback,
particle positions are linearly interpolated between accepted states and the
Voronoi mesh is reconstructed for each display frame. These intermediate display
frames are visual interpolation, not extra solver steps. The initial and final
frames use the exact recorded positions; both final numerical states have been
checked against the saved Figure 1 data.

## Longer runs

Both variants are also available through **t = 1.5** in
[extended-t1p5](extended-t1p5/), with MP4s, GIF previews, final-frame PNGs, and
verification details. They use the same solver settings and preserve the
original playback speed, with a two-second hold on the final frame. The
original t = 1 movies above are unchanged.
