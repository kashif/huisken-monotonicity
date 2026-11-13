"""Figures for the blueprint.

The figures are computed for curves in the plane (n = 1, E = R^2), where mean curvature flow
is the curve shortening flow and the kernel is
rho(x, t) = (4 pi (t0 - t))^(-1/2) exp(-|x - x0|^2 / (4 (t0 - t))),
except for the shaded sphere, which is the case n = 2.

Run from the repository root:  python blueprint/figures/make_figures.py
Outputs go to blueprint/src/figures/<name>.{pdf,png}.
"""

from __future__ import annotations

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402
from matplotlib.collections import LineCollection  # noqa: E402
from matplotlib.colors import LinearSegmentedColormap, PowerNorm  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402

OUT = Path(__file__).resolve().parents[1] / "src" / "figures"

PALETTE = {
    "blue_main": "#0F4D92",
    "blue_secondary": "#3775BA",
    "green_1": "#DDF3DE",
    "green_2": "#AADCA9",
    "green_3": "#8BCF8B",
    "red_1": "#F6CFCB",
    "red_2": "#E9A6A1",
    "red_strong": "#B64342",
    "neutral": "#CFCECE",
    "grey": "#767676",
    "dark": "#272727",
    "teal": "#42949E",
    "violet": "#9A4D8E",
}
GREEN = "#3E9B4F"  # a darker green for arrows, from the same family

plt.rcParams.update(
    {
        "font.family": ["Arial", "Helvetica", "DejaVu Sans", "sans-serif"],
        "font.size": 15,
        "axes.linewidth": 2,
        "axes.spines.right": False,
        "axes.spines.top": False,
        "legend.frameon": False,
        "mathtext.fontset": "cm",
        "pdf.fonttype": 42,
        "svg.fonttype": "none",
        "savefig.dpi": 300,
    }
)

SPOT = LinearSegmentedColormap.from_list("spot", ["#FFFFFF", "#DCE8F5", "#3775BA", "#0F4D92"])
LOSS = LinearSegmentedColormap.from_list("loss", [PALETTE["neutral"], PALETTE["red_2"], PALETTE["red_strong"]])


# ---------------------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------------------


def save(fig, name: str) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    for ext in ("pdf", "png"):
        fig.savefig(OUT / f"{name}.{ext}", bbox_inches="tight", pad_inches=0.05)
    plt.close(fig)


def blank(ax) -> None:
    """A conceptual panel: equal aspect, no axes."""
    ax.set_aspect("equal")
    ax.set_axis_off()


def callout(ax, xy, text, color, xytext=None, fontsize=14, ha="center"):
    """A label in a white box, optionally joined to `xy` by a thin line."""
    box = {"boxstyle": "round,pad=0.25", "fc": "white", "ec": "none", "alpha": 0.92}
    if xytext is None:
        ax.text(*xy, text, color=color, fontsize=fontsize, ha=ha, va="center", bbox=box, zorder=6)
    else:
        ax.annotate(text, xy=xy, xytext=xytext, color=color, fontsize=fontsize, ha=ha, va="center",
                    bbox=box, zorder=6, arrowprops={"arrowstyle": "-", "color": color, "lw": 1.2})


def arrows(ax, base, vec, color, scale=1.0, lw=2.2, ms=14, zorder=4):
    for p, v in zip(base, vec):
        if np.linalg.norm(v) * scale < 1e-3:
            continue
        ax.annotate("", xy=p + scale * v, xytext=p, zorder=zorder,
                    arrowprops={"arrowstyle": "-|>", "color": color, "lw": lw, "mutation_scale": ms,
                                "shrinkA": 0, "shrinkB": 0})


def closed(x):
    return np.vstack([x, x[:1]])


def kernel(x: np.ndarray, tau: float, n: int = 1) -> np.ndarray:
    """The backward heat kernel at `tau = t0 - t`, centred at the origin."""
    r2 = np.sum(x * x, axis=-1)
    return (4 * np.pi * tau) ** (-n / 2) * np.exp(-r2 / (4 * tau))


def shaded_sphere(ax, radius, light=(-0.5, 0.55, 0.75), res=500):
    """A Lambert-shaded disk, read as a sphere (as in the figures4papers illustrations)."""
    g = np.linspace(-1, 1, res)
    X, Y = np.meshgrid(g, g)
    r2 = X ** 2 + Y ** 2
    inside = r2 <= 1
    Z = np.sqrt(np.clip(1 - r2, 0, 1))
    L = np.array(light) / np.linalg.norm(light)
    shade = np.clip(0.5 + 0.55 * (X * L[0] + Y * L[1] + Z * L[2]), 0, 1)
    img = np.ones((res, res, 4))
    img[..., :3] = shade[..., None]
    img[..., 3] = inside
    ax.imshow(img, extent=[-radius, radius, -radius, radius], origin="lower", zorder=1)


# ---------------------------------------------------------------------------------------
# Curve shortening flow of a closed polygon
# ---------------------------------------------------------------------------------------


def resample(x: np.ndarray, m: int) -> np.ndarray:
    """Resample a closed polygon to `m` points equally spaced in arclength."""
    seg = np.linalg.norm(np.roll(x, -1, axis=0) - x, axis=1)
    s = np.concatenate([[0.0], np.cumsum(seg)])
    t = np.linspace(0.0, s[-1], m, endpoint=False)
    xc = closed(x)
    return np.stack([np.interp(t, s, xc[:, 0]), np.interp(t, s, xc[:, 1])], axis=1)


def geometry(x: np.ndarray):
    """Arclength weights, unit tangent, curvature vector (central differences)."""
    xp, xm = np.roll(x, -1, axis=0), np.roll(x, 1, axis=0)
    hp = np.linalg.norm(xp - x, axis=1)
    hm = np.linalg.norm(x - xm, axis=1)
    ds = 0.5 * (hp + hm)
    tangent = (xp - xm) / (hp + hm)[:, None]
    tangent /= np.linalg.norm(tangent, axis=1)[:, None]
    second = 2 * ((xp - x) / hp[:, None] - (x - xm) / hm[:, None]) / (hp + hm)[:, None]
    hvec = second - np.sum(second * tangent, axis=1)[:, None] * tangent
    return ds, tangent, hvec


def normal_part(x, tangent):
    return x - np.sum(x * tangent, axis=1)[:, None] * tangent


def area(x: np.ndarray) -> float:
    return 0.5 * abs(np.sum(x[:, 0] * np.roll(x[:, 1], -1) - np.roll(x[:, 0], -1) * x[:, 1]))


def curve_shortening(x0: np.ndarray, t_end: float):
    """Explicit curve shortening flow `dx/dt = H`, resampled to keep points uniform."""
    x, t, m = x0.copy(), 0.0, len(x0)
    hist = []
    while t < t_end:
        ds, _, hvec = geometry(x)
        hist.append((t, x.copy()))
        dt = min(0.2 * ds.min() ** 2, t_end - t)
        x = resample(x + dt * hvec, m)
        t += dt
    return hist


def ellipse(a: float, b: float, m: int) -> np.ndarray:
    th = np.linspace(0, 2 * np.pi, m, endpoint=False)
    return resample(np.stack([a * np.cos(th), b * np.sin(th)], axis=1), m)


def at_time(hist, t):
    ts = np.array([s for s, _ in hist])
    i = min(np.searchsorted(ts, t), len(ts) - 1)
    return ts[i], hist[i][1]


def local_terms(x, tau):
    """Pointwise kernel, defect vector `H + x^perp / 2 tau`, and its weighted square."""
    ds, tangent, hvec = geometry(x)
    rho = kernel(x, tau)
    defect = hvec + normal_part(x, tangent) / (2 * tau)
    loss = rho * np.sum(defect * defect, axis=1)
    return ds, rho, defect, loss


# The ellipse with semi-axes 2, 1 has area 2 pi; a closed curve loses area at rate 2 pi, so it
# shrinks to a round point at the origin at time T = 1 (Gage-Hamilton, Grayson). T is reset to
# the extinction time of the discrete flow, t + A(t) / 2 pi, so the kernel is centred where the
# discrete curve vanishes.
A, B, T = 2.0, 1.0, 1.0
M = 400


def run_ellipse():
    global T
    hist = curve_shortening(ellipse(A, B, M), 0.95 * T)
    t_last, x_last = hist[-1]
    T = t_last + area(x_last) / (2 * np.pi)
    return hist


def series(hist, k=400):
    ts = np.array([t for t, _ in hist])
    sel = np.unique(np.searchsorted(ts, np.linspace(0, ts[-1], k)))
    sel = sel[sel < len(ts)]
    return ts[sel], [hist[i][1] for i in sel]


# ---------------------------------------------------------------------------------------
# Figure 1: what the kernel measures
# ---------------------------------------------------------------------------------------


def fig_kernel() -> None:
    fig, axes = plt.subplots(1, 3, figsize=(15, 4.4), gridspec_kw={"width_ratios": [1.1, 1, 1.1]})

    ax = axes[0]
    xs = np.linspace(-3, 3, 600)
    taus = [1.0, 0.3, 0.06]
    cols = [PALETTE["neutral"], PALETTE["blue_secondary"], PALETTE["blue_main"]]
    for tau, c in zip(taus, cols):
        y = kernel(xs[:, None], tau)
        ax.fill_between(xs, y, color=c, alpha=0.18, lw=0)
        ax.plot(xs, y, color=c, lw=2.5, label=rf"$t_0 - t = {tau:g}$")
    ax.set_xlabel(r"$x$")
    ax.set_yticks([])
    ax.spines["left"].set_visible(False)
    ax.legend(fontsize=13, loc="upper right")
    ax.set_title("(a) area one at every scale", fontsize=15)

    ax = axes[1]
    tau, d = 0.15, 0.9
    g = np.linspace(-1.7, 1.7, 400)
    X, Y = np.meshgrid(g, g)
    ax.imshow(kernel(np.stack([X, Y], -1), tau, n=2), extent=[-1.7, 1.7, -1.7, 1.7], origin="lower",
              cmap=SPOT, zorder=0)
    r = np.sqrt(2 * tau)
    th = np.linspace(0, 2 * np.pi, 200)
    ax.plot(r * np.cos(th), r * np.sin(th), color=PALETTE["dark"], lw=1.2, ls=(0, (4, 3)))
    ax.plot([-1.7, 1.7], [0, 0], color=GREEN, lw=3)
    ax.plot([-1.7, 1.7], [d, d], color=PALETTE["red_strong"], lw=3)
    ax.plot([0], [0], "o", color="white", mec=PALETTE["dark"], ms=7, zorder=5)
    callout(ax, (0.0, 0.25), r"$x_0$", PALETTE["dark"], fontsize=14)
    callout(ax, (-1.0, 0.0), "through $x_0$", GREEN, fontsize=13)
    callout(ax, (-0.95, d), "missing $x_0$", PALETTE["red_strong"], fontsize=13)
    callout(ax, (r * np.cos(-0.7), r * np.sin(-0.7)), r"scale $\sqrt{t_0 - t}$", PALETTE["dark"],
            xytext=(0.9, -1.25), fontsize=13)
    blank(ax)
    ax.set_title("(b) a spotlight at $x_0$", fontsize=15)

    ax = axes[2]
    t0 = 1.0
    t = np.linspace(0, t0 - 1e-3, 400)
    ax.plot(t, np.ones_like(t), color=GREEN, lw=3, label="line through $x_0$")
    ax.plot(t, np.exp(-d ** 2 / (4 * (t0 - t))), color=PALETTE["red_strong"], lw=3, label="line missing $x_0$")
    ax.set_xlabel(r"$t \to t_0$")
    ax.set_ylabel(r"$\int \rho\, d\mu$")
    ax.set_ylim(-0.05, 1.25)
    ax.set_xticks([0, t0], ["0", "$t_0$"])
    ax.legend(fontsize=13, loc="lower left")
    ax.set_title("(c) the density of a line", fontsize=15)
    fig.tight_layout(pad=1)
    save(fig, "kernel")


# ---------------------------------------------------------------------------------------
# Figure 2: when does the integrand vanish?
# ---------------------------------------------------------------------------------------


def fig_integrand(hist) -> None:
    fig, axes = plt.subplots(1, 2, figsize=(12, 5.6))

    # (a) the sphere of radius sqrt(2 n tau), n = 2: H and x^perp / 2 tau cancel
    ax = axes[0]
    n, tau = 2, 0.5
    R = np.sqrt(2 * n * tau)
    shaded_sphere(ax, R)
    pts = []
    for a in np.linspace(0, 2 * np.pi, 12, endpoint=False):  # the outline
        pts.append([R * np.cos(a), R * np.sin(a)])
    pts = np.array(pts)
    radial = pts / R  # the projection of the unit normal p / R
    h = -(n / R) * radial  # H = -(n / R^2) x
    q = (R / (2 * tau)) * radial  # x^perp / 2 tau = x / 2 tau
    arrows(ax, pts, q, PALETTE["blue_main"], scale=0.45)
    arrows(ax, pts, h, PALETTE["red_strong"], scale=0.45)
    callout(ax, (0, -2.25), r"$\vec H + \frac{x^\perp}{2(t_0 - t)} = 0$: the integrand vanishes", GREEN,
            fontsize=14)
    callout(ax, (0.0, 2.45), r"$x^\perp / 2(t_0 - t)$ pushes out", PALETTE["blue_main"], fontsize=13)
    callout(ax, (0.0, 0.0), r"$\vec H$ pulls in" + "\nby the same amount", PALETTE["red_strong"], fontsize=13)
    lim = 2.05
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-2.45, 2.7)
    blank(ax)
    ax.set_title(r"(a) the sphere of radius $\sqrt{2n(t_0 - t)}$", fontsize=15)

    # (b) the ellipse at t = 0.6, centred at its extinction point: they do not cancel
    ax = axes[1]
    t, x = at_time(hist, 0.6)
    tau = T - t
    _, tangent, hvec = geometry(x)
    q = normal_part(x, tangent) / (2 * tau)
    d = hvec + q
    ax.plot(*closed(x).T, color=PALETTE["dark"], lw=2.5, zorder=2)
    idx = np.linspace(0, len(x), 14, endpoint=False).astype(int)
    arrows(ax, x[idx], q[idx], PALETTE["blue_main"], scale=0.28, lw=1.6, ms=11)
    arrows(ax, x[idx], hvec[idx], PALETTE["red_strong"], scale=0.28, lw=1.6, ms=11)
    arrows(ax, x[idx], d[idx], GREEN, scale=0.28 * 2.5, lw=3, ms=16, zorder=5)
    ax.plot([0], [0], "o", color="white", mec=PALETTE["dark"], ms=7)
    callout(ax, (0.0, -0.2), r"$x_0$", PALETTE["dark"], fontsize=14)
    i_tip = np.argmax(x[:, 0])
    callout(ax, x[i_tip] + 0.28 * 2.5 * d[i_tip], "more curved than a shrinker:\nmoves in faster", GREEN,
            xytext=(1.0, 1.25), fontsize=13)
    i_side = np.argmin(x[:, 1])
    callout(ax, x[i_side] + 0.28 * 2.5 * d[i_side], "flatter than a shrinker:\nmoves in slower", GREEN,
            xytext=(-0.6, -1.5), fontsize=13)
    ax.set_xlim(-lim * 0.9, lim * 0.9)
    ax.set_ylim(-lim * 0.9, lim * 0.9)
    blank(ax)
    ax.set_title(r"(b) the ellipse at $t = 0.6$", fontsize=15)

    handles = [
        Line2D([], [], color=PALETTE["red_strong"], lw=3, label=r"$\vec H$"),
        Line2D([], [], color=PALETTE["blue_main"], lw=3, label=r"$\frac{x^\perp}{2(t_0 - t)}$"),
        Line2D([], [], color=GREEN, lw=3, label=r"$\vec H + \frac{x^\perp}{2(t_0 - t)}$ (enlarged)"),
    ]
    fig.legend(handles=handles, loc="lower center", ncol=3, fontsize=15, bbox_to_anchor=(0.5, -0.02))
    fig.tight_layout(rect=(0, 0.07, 1, 1), pad=1)
    save(fig, "integrand")


# ---------------------------------------------------------------------------------------
# Figure 3: where the density is lost
# ---------------------------------------------------------------------------------------


def fig_monotone(hist) -> None:
    fig, axes = plt.subplots(1, 3, figsize=(16, 4.8), gridspec_kw={"width_ratios": [1.15, 1, 1]})

    ax = axes[0]
    snaps = [0.0, 0.3, 0.6, 0.8, 0.9, 0.94]
    curves = []
    for s in snaps:
        t, x = at_time(hist, s)
        _, _, _, loss = local_terms(x, T - t)
        curves.append((x, loss))
    vmax = max(loss.max() for _, loss in curves)
    norm = PowerNorm(0.5, vmin=0, vmax=vmax)
    for x, loss in curves:
        xc = closed(x)
        segs = np.stack([xc[:-1], xc[1:]], axis=1)
        lc = LineCollection(segs, cmap=LOSS, norm=norm, lw=4, capstyle="round")
        lc.set_array(loss)
        ax.add_collection(lc)
    ax.plot([0], [0], "o", color="white", mec=PALETTE["dark"], ms=7)
    callout(ax, (0.0, -0.32), r"$(x_0, t_0)$", PALETTE["dark"], fontsize=13)
    callout(ax, (2.0, 0.0), "most loss\nat the tips", PALETTE["red_strong"], xytext=(1.6, 1.35), fontsize=13)
    callout(ax, (-0.25, 0.25), "nearly round:\nlittle loss", PALETTE["grey"], xytext=(-1.35, 1.35), fontsize=13)
    ax.set_xlim(-2.2, 2.2)
    ax.set_ylim(-1.6, 1.7)
    blank(ax)
    cb = fig.colorbar(plt.cm.ScalarMappable(norm=norm, cmap=LOSS), ax=ax, orientation="horizontal",
                      fraction=0.05, pad=0.02, ticks=[])
    cb.set_label(r"local loss $\rho\,|\vec H + x^\perp / 2(t_0 - t)|^2$", fontsize=13)
    cb.outline.set_visible(False)
    ax.set_title(r"(a) the ellipse, $t = 0, \ldots, 0.94$", fontsize=15)

    tt, xs = series(hist)
    th, rh = [], []
    for t, x in zip(tt, xs):
        ds, rho, _, loss = local_terms(x, T - t)
        th.append(np.sum(rho * ds))
        rh.append(-np.sum(loss * ds))
    th, rh = np.array(th), np.array(rh)
    limit = np.sqrt(2 * np.pi / np.e)

    ax = axes[1]
    ax.fill_between(tt, limit, th, color=PALETTE["red_1"], lw=0)
    ax.plot(tt, th, color=PALETTE["blue_main"], lw=3)
    ax.axhline(limit, color=PALETTE["grey"], ls="--", lw=1.8)
    callout(ax, (0.3, limit + 0.003), r"shrinking circle: $\sqrt{2\pi / e}$", PALETTE["grey"], fontsize=13)
    callout(ax, (0.3, th[0] - 0.012), r"$\int \rho\, d\mu_t$", PALETTE["blue_main"], fontsize=15)
    ax.set_xlabel(r"$t$")
    ax.set_title("(b) the Gaussian density decreases", fontsize=15)

    ax = axes[2]
    ax.plot(tt, np.gradient(th, tt), color=PALETTE["blue_main"], lw=3, label=r"$\frac{d}{dt}\int \rho\, d\mu_t$")
    ax.plot(tt[::14], rh[::14], "o", color=PALETTE["red_strong"], ms=6,
            label=r"$-\int \rho\, |\vec H + \frac{x^\perp}{2(t_0-t)}|^2 d\mu_t$")
    ax.set_xlabel(r"$t$")
    ax.legend(fontsize=14, loc="lower right")
    ax.set_title("(c) the two sides of Theorem 3.1", fontsize=15)
    fig.tight_layout(pad=1)
    save(fig, "monotone")


# ---------------------------------------------------------------------------------------
# Figure 4: the rescaled flow
# ---------------------------------------------------------------------------------------


def fig_rescaled(hist) -> None:
    fig, axes = plt.subplots(1, 3, figsize=(16, 4.8), gridspec_kw={"width_ratios": [1, 1, 1.1]})
    blues = plt.get_cmap("Blues")
    s_of = lambda t: -0.5 * np.log(T - t)  # noqa: E731
    s_snap = [s_of(0.0), 0.25, 0.5, 0.8, 1.5]

    for k, s in enumerate(s_snap):
        t, x = at_time(hist, T - np.exp(-2 * s))
        c = blues(0.35 + 0.65 * k / (len(s_snap) - 1))
        axes[0].plot(*closed(x).T, color=c, lw=2.5)
        y = x / np.sqrt(2 * (T - t))
        axes[1].plot(*closed(y).T, color=c, lw=2.5)
    for ax in axes[:2]:
        ax.set_xlim(-2.2, 2.2)
        ax.set_ylim(-1.7, 1.7)
        blank(ax)
    axes[0].plot([0], [0], "o", color=PALETTE["red_strong"], ms=6)
    callout(axes[0], (0, 0), "vanishes at\n$(0, T)$", PALETTE["red_strong"], xytext=(1.25, -1.3), fontsize=13)
    axes[0].set_title("(a) the flow shrinks to a point", fontsize=15)
    th = np.linspace(0, 2 * np.pi, 200)
    axes[1].plot(np.cos(th), np.sin(th), color=PALETTE["red_strong"], ls="--", lw=2)
    callout(axes[1], (np.cos(-2.3), np.sin(-2.3)), r"self-shrinker $|y| = \sqrt{n}$", PALETTE["red_strong"],
            xytext=(-0.9, -1.45), fontsize=13)
    axes[1].set_title(r"(b) magnified by $1/\sqrt{2(T - t)}$", fontsize=15)
    fig.text(0.355, 0.5, r"$\Longrightarrow$", fontsize=26, ha="center", va="center", color=PALETTE["grey"])

    ax = axes[2]
    tt, xs = series(hist, 300)
    ss, vals = [], []
    for t, x in zip(tt, xs):
        y = x / np.sqrt(2 * (T - t))
        ds, _, _ = geometry(y)
        vals.append(np.sum(np.exp(-np.sum(y * y, axis=1) / 2) * ds))
        ss.append(s_of(t))
    lim = 2 * np.pi / np.sqrt(np.e)
    ax.fill_between(ss, lim, vals, color=PALETTE["red_1"], lw=0)
    ax.plot(ss, vals, color=PALETTE["blue_main"], lw=3)
    ax.axhline(lim, color=PALETTE["grey"], ls="--", lw=1.8)
    callout(ax, (0.35, lim + 0.008), r"unit circle: $2\pi e^{-1/2}$", PALETTE["grey"], fontsize=13)
    callout(ax, (0.55, vals[0] - 0.03), r"$\int \tilde\rho\, d\tilde\mu_s$", PALETTE["blue_main"], fontsize=15)
    ax.set_xlabel(r"$s = -\frac{1}{2}\log(T - t)$")
    ax.set_title("(c) the rescaled density decreases", fontsize=15)
    fig.tight_layout(pad=1)
    save(fig, "rescaled")


# ---------------------------------------------------------------------------------------
# Figure 5: the shrinking sphere, the equality case
# ---------------------------------------------------------------------------------------


def fig_sphere() -> None:
    fig, axes = plt.subplots(1, 2, figsize=(13, 5.0), gridspec_kw={"width_ratios": [1, 1.1]})
    Ts = 0.5  # R(t)^2 = 1 - 2t

    # (a) space-time: the track of the circle and the scale of the kernel
    ax = axes[0]
    xg = np.linspace(-1.3, 1.3, 500)
    tg = np.linspace(0, Ts - 1e-3, 400)
    Xg, Tg = np.meshgrid(xg, tg)
    rho = np.exp(-Xg ** 2 / (4 * (Ts - Tg)))  # each time row scaled to peak one
    ax.imshow(rho, extent=[xg[0], xg[-1], 0, Ts], origin="lower", aspect="auto", cmap=SPOT, alpha=0.5)
    t = np.linspace(0, Ts, 400)
    R = np.sqrt(1 - 2 * t)
    ax.fill_betweenx(t, -R, R, color="white", alpha=0.0)
    ax.plot(R, t, color=PALETTE["blue_main"], lw=4)
    ax.plot(-R, t, color=PALETTE["blue_main"], lw=4)
    ax.plot(np.sqrt(2 * (Ts - t)), t, color=GREEN, lw=2, ls=(0, (5, 3)))
    ax.plot(-np.sqrt(2 * (Ts - t)), t, color=GREEN, lw=2, ls=(0, (5, 3)))
    t07 = 0.7
    ax.plot(np.sqrt(2 * (t07 - t)), t, color=PALETTE["teal"], lw=2, ls=":")
    ax.plot(-np.sqrt(2 * (t07 - t)), t, color=PALETTE["teal"], lw=2, ls=":")
    ax.plot([0], [Ts], "o", color="white", mec=PALETTE["dark"], ms=8, zorder=5, clip_on=False)
    callout(ax, (0.0, Ts * 0.93), r"$(0, T)$", PALETTE["dark"], fontsize=13)
    callout(ax, (np.sqrt(1 - 2 * 0.25), 0.25), "the circle $|F| = R(t)$", PALETTE["blue_main"],
            xytext=(1.0, 0.33), fontsize=13)
    callout(ax, (-np.sqrt(2 * (Ts - 0.3)), 0.3), "kernel scale for $(0, T)$:\nthe same curve",
            GREEN, xytext=(-0.72, 0.4), fontsize=13)
    callout(ax, (-np.sqrt(2 * (t07 - 0.12)), 0.12), "scale for $(0, 0.7)$", PALETTE["teal"],
            xytext=(-0.55, 0.12), fontsize=13)
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$t$")
    ax.set_xlim(-1.3, 1.3)
    ax.set_ylim(0, Ts)
    ax.set_title("(a) space-time: the circle fills the spotlight", fontsize=15)

    # (b) the density for four centres
    ax = axes[1]
    phi = np.linspace(0, 2 * np.pi, 2000, endpoint=False)

    def theta(t, x0, t0):
        R = np.sqrt(1 - 2 * t)
        pts = np.stack([R * np.cos(phi) - x0[0], R * np.sin(phi) - x0[1]], axis=1)
        return np.mean(kernel(pts, t0 - t)) * 2 * np.pi * R

    cases = [
        ((0.0, 0.0), Ts, GREEN, r"$(0, T)$: constant"),
        ((0.0, 0.0), 0.7, PALETTE["teal"], r"$(0, 0.7)$"),
        ((0.4, 0.0), Ts, PALETTE["violet"], r"$((0.4, 0), T)$"),
        ((0.0, 0.0), 0.4, PALETTE["red_2"], r"$(0, 0.4)$"),
    ]
    for x0, t0, c, lab in cases:
        tt = np.linspace(0, min(t0, Ts) - 1e-3, 300)
        ax.plot(tt, [theta(s, x0, t0) for s in tt], color=c, lw=3, label=lab)
    ax.set_xlabel(r"$t$")
    ax.set_ylabel(r"$\int \rho_{x_0, t_0}\, d\mu_t$")
    ax.set_xticks([0, 0.25, Ts], ["0", "0.25", "$T$"])
    ax.legend(fontsize=13, loc="lower left", title=r"centre $(x_0, t_0)$", title_fontsize=13)
    ax.set_title("(b) the density for four centres", fontsize=15)
    fig.tight_layout(pad=1)
    save(fig, "sphere")


def main() -> None:
    fig_kernel()
    fig_sphere()
    hist = run_ellipse()
    fig_integrand(hist)
    fig_monotone(hist)
    fig_rescaled(hist)


if __name__ == "__main__":
    main()
