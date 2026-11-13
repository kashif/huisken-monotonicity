"""Figures for the blueprint.

Every figure is computed for a curve in the plane (n = 1, E = R^2), where mean curvature
flow is the curve shortening flow and the kernel is
rho(x, t) = (4 pi (t0 - t))^(-1/2) exp(-|x - x0|^2 / (4 (t0 - t))).

Run from the repository root:  python blueprint/figures/make_figures.py
Outputs go to blueprint/src/figures/<name>.{pdf,png}.
"""

from __future__ import annotations

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

OUT = Path(__file__).resolve().parents[1] / "src" / "figures"

PALETTE = {
    "blue_main": "#0F4D92",
    "blue_secondary": "#3775BA",
    "green_3": "#8BCF8B",
    "red_strong": "#B64342",
    "red_2": "#E9A6A1",
    "neutral": "#CFCECE",
    "grey": "#767676",
    "teal": "#42949E",
    "violet": "#9A4D8E",
}

plt.rcParams.update(
    {
        "font.family": ["Arial", "Helvetica", "DejaVu Sans", "sans-serif"],
        "font.size": 13,
        "axes.linewidth": 1.5,
        "axes.spines.right": False,
        "axes.spines.top": False,
        "legend.frameon": False,
        "mathtext.fontset": "cm",
        "pdf.fonttype": 42,
        "savefig.dpi": 300,
    }
)


def save(fig, name: str) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    fig.tight_layout(pad=1)
    for ext in ("pdf", "png"):
        fig.savefig(OUT / f"{name}.{ext}", bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)


def kernel(x: np.ndarray, tau: float, n: int = 1) -> np.ndarray:
    """The backward heat kernel at `tau = t0 - t`, centred at the origin."""
    r2 = np.sum(x * x, axis=-1)
    return (4 * np.pi * tau) ** (-n / 2) * np.exp(-r2 / (4 * tau))


# ---------------------------------------------------------------------------------------
# Curve shortening flow of a closed polygon
# ---------------------------------------------------------------------------------------


def resample(x: np.ndarray, m: int) -> np.ndarray:
    """Resample a closed polygon to `m` points equally spaced in arclength."""
    seg = np.linalg.norm(np.roll(x, -1, axis=0) - x, axis=1)
    s = np.concatenate([[0.0], np.cumsum(seg)])
    t = np.linspace(0.0, s[-1], m, endpoint=False)
    xc = np.vstack([x, x[:1]])
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
    # the curvature vector is the normal part of d^2x/ds^2
    hvec = second - np.sum(second * tangent, axis=1)[:, None] * tangent
    return ds, tangent, hvec


def curve_shortening(x0: np.ndarray, t_end: float, snapshots: list[float]):
    """Explicit curve shortening flow `dx/dt = H`, resampled to keep points uniform."""
    x, t = x0.copy(), 0.0
    m = len(x0)
    times, frames, hist = [], [], []
    snaps = sorted(snapshots)
    while t < t_end:
        ds, _, hvec = geometry(x)
        hist.append((t, x.copy()))
        while snaps and t >= snaps[0]:
            frames.append((snaps.pop(0), x.copy()))
        dt = min(0.2 * ds.min() ** 2, t_end - t)
        x = resample(x + dt * hvec, m)
        t += dt
        times.append(t)
    return frames, hist


def ellipse(a: float, b: float, m: int) -> np.ndarray:
    th = np.linspace(0, 2 * np.pi, m, endpoint=False)
    return resample(np.stack([a * np.cos(th), b * np.sin(th)], axis=1), m)


def density_terms(x: np.ndarray, tau: float):
    """Gaussian density and the right-hand side of Huisken's formula on a polygon."""
    ds, tangent, hvec = geometry(x)
    rho = kernel(x, tau)
    normal_pos = x - np.sum(x * tangent, axis=1)[:, None] * tangent
    defect = hvec + normal_pos / (2 * tau)
    theta = np.sum(rho * ds)
    rhs = -np.sum(rho * np.sum(defect * defect, axis=1) * ds)
    return theta, rhs


# The ellipse with semi-axes 2, 1 has area 2 pi; a closed curve loses area at rate 2 pi,
# so it shrinks to a round point at the origin at time T = 1 (Gage-Hamilton, Grayson).
A, B, T = 2.0, 1.0, 1.0
M = 400
SNAPS = [0.0, 0.3, 0.6, 0.8, 0.9, 0.94]


def area(x: np.ndarray) -> float:
    return 0.5 * abs(np.sum(x[:, 0] * np.roll(x[:, 1], -1) - np.roll(x[:, 0], -1) * x[:, 1]))


def run_ellipse():
    """Run the flow to `0.95 T`, and set `T` to the extinction time of the discrete flow,
    `t + A(t) / 2 pi`, so that the kernel is centred where the discrete curve vanishes."""
    global T
    frames, hist = curve_shortening(ellipse(A, B, M), 0.95 * T, SNAPS)
    t_last, x_last = hist[-1]
    T = t_last + area(x_last) / (2 * np.pi)
    return frames, hist


# ---------------------------------------------------------------------------------------
# Figure 1: the backward heat kernel
# ---------------------------------------------------------------------------------------


def fig_kernel() -> None:
    fig, axes = plt.subplots(1, 2, figsize=(10, 3.4))
    ax = axes[0]
    xs = np.linspace(-3, 3, 600)
    taus = [1.0, 0.4, 0.15, 0.05]
    colors = [PALETTE["neutral"], PALETTE["blue_secondary"], PALETTE["teal"], PALETTE["blue_main"]]
    for tau, c in zip(taus, colors):
        ax.plot(xs, kernel(xs[:, None], tau), color=c, lw=2.2, label=rf"$t_0 - t = {tau:g}$")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$\rho(x, t)$")
    ax.set_title(r"(a) $n = 1$: unit mass, concentrating as $t \to t_0$", fontsize=12)
    ax.legend(fontsize=11)

    ax = axes[1]
    g = np.linspace(-2.2, 2.2, 300)
    X, Y = np.meshgrid(g, g)
    tau = 0.25
    Z = kernel(np.stack([X, Y], axis=-1), tau, n=2)
    ax.contourf(X, Y, Z, levels=14, cmap="Blues")
    th = np.linspace(0, 2 * np.pi, 200)
    r = np.sqrt(2 * 2 * tau)
    ax.plot(r * np.cos(th), r * np.sin(th), color=PALETTE["red_strong"], lw=2, ls="--")
    ax.annotate(
        r"$|x|^2 = 2n(t_0 - t)$",
        xy=(r * np.cos(0.8), r * np.sin(0.8)),
        xytext=(1.0, 1.85),
        color=PALETTE["red_strong"],
        fontsize=12,
        arrowprops={"arrowstyle": "-", "color": PALETTE["red_strong"]},
    )
    ax.set_aspect("equal")
    ax.set_xticks([])
    ax.set_yticks([])
    for s in ("left", "bottom"):
        ax.spines[s].set_visible(False)
    ax.set_title(r"(b) $n = 2$, $t_0 - t = 1/4$", fontsize=12)
    save(fig, "kernel")


# ---------------------------------------------------------------------------------------
# Figure 2: the integrand H + x^perp / 2 tau
# ---------------------------------------------------------------------------------------


def fig_integrand(frames) -> None:
    fig, axes = plt.subplots(1, 2, figsize=(10, 4.0))
    tau_c = 0.5
    r = np.sqrt(2 * tau_c)
    circle = ellipse(r, r, 400)
    x_ell = dict(frames)[0.6]
    tau_e = T - 0.6
    for ax, x, tau, title in (
        (axes[0], circle, tau_c, r"(a) circle of radius $\sqrt{2(t_0 - t)}$"),
        (axes[1], x_ell, tau_e, r"(b) the ellipse at $t = 0.6$, $(x_0, t_0) = (0, T)$"),
    ):
        _, tangent, hvec = geometry(x)
        normal_pos = x - np.sum(x * tangent, axis=1)[:, None] * tangent
        q = normal_pos / (2 * tau)
        ax.plot(*np.vstack([x, x[:1]]).T, color="black", lw=1.8)
        idx = np.linspace(0, len(x), 16, endpoint=False).astype(int)
        kw = {"angles": "xy", "scale_units": "xy", "scale": 2.2, "width": 0.006}
        ax.quiver(*x[idx].T, *hvec[idx].T, color=PALETTE["red_strong"], **kw)
        ax.quiver(*x[idx].T, *q[idx].T, color=PALETTE["blue_main"], **kw)
        d = hvec + q
        ax.quiver(*x[idx].T, *d[idx].T, color=PALETTE["green_3"], **kw, zorder=3)
        ax.plot([0], [0], "o", color=PALETTE["grey"], ms=4)
        ax.set_aspect("equal")
        ax.set_xticks([])
        ax.set_yticks([])
        for s in ("left", "bottom"):
            ax.spines[s].set_visible(False)
        ax.set_title(title, fontsize=12)
        lim = 1.45 * np.abs(x).max()
        ax.set_xlim(-lim, lim)
        ax.set_ylim(-lim, lim)
    handles = [
        plt.Line2D([], [], color=PALETTE["red_strong"], lw=3, label=r"$\vec H$"),
        plt.Line2D([], [], color=PALETTE["blue_main"], lw=3, label=r"$x^\perp / 2(t_0 - t)$"),
        plt.Line2D([], [], color=PALETTE["green_3"], lw=3, label=r"$\vec H + x^\perp / 2(t_0 - t)$"),
    ]
    fig.legend(handles=handles, loc="lower center", ncol=3, fontsize=12, bbox_to_anchor=(0.5, -0.04))
    fig.tight_layout(rect=(0, 0.06, 1, 1))
    save(fig, "integrand")


# ---------------------------------------------------------------------------------------
# Figure 3: the ellipse under curve shortening flow
# ---------------------------------------------------------------------------------------


def fig_monotone(frames, hist) -> None:
    fig, axes = plt.subplots(1, 3, figsize=(14, 3.9), gridspec_kw={"width_ratios": [1.1, 1, 1]})
    ax = axes[0]
    cmap = plt.get_cmap("Blues")
    for k, (t, x) in enumerate(frames):
        ax.plot(*np.vstack([x, x[:1]]).T, color=cmap(0.35 + 0.65 * k / (len(frames) - 1)), lw=2)
    ax.plot([0], [0], "o", color=PALETTE["red_strong"], ms=5)
    ax.annotate(r"$(x_0, t_0) = (0, T)$", (0, 0), xytext=(0.3, -1.25), fontsize=11, color=PALETTE["red_strong"])
    ax.set_aspect("equal")
    ax.set_xticks([])
    ax.set_yticks([])
    for s in ("left", "bottom"):
        ax.spines[s].set_visible(False)
    ax.set_title(r"(a) $t = " + ", ".join(f"{t:g}" for t, _ in frames) + "$", fontsize=11)

    ts = np.array([t for t, _ in hist])
    sel = np.unique(np.searchsorted(ts, np.linspace(0, ts[-1], 400)))
    sel = sel[sel < len(ts)]
    th, rh = [], []
    for i in sel:
        theta, rhs = density_terms(hist[i][1], T - ts[i])
        th.append(theta)
        rh.append(rhs)
    th, rh, tt = np.array(th), np.array(rh), ts[sel]

    ax = axes[1]
    ax.plot(tt, th, color=PALETTE["blue_main"], lw=2.5, label=r"$\int \rho\, d\mu_t$")
    ax.axhline(np.sqrt(2 * np.pi / np.e), color=PALETTE["grey"], ls="--", lw=1.5, label=r"circle: $\sqrt{2\pi/e}$")
    ax.set_xlabel(r"$t$")
    ax.set_title("(b) the Gaussian density decreases", fontsize=12)
    ax.legend(fontsize=11)

    ax = axes[2]
    dth = np.gradient(th, tt)
    ax.plot(tt, dth, color=PALETTE["blue_main"], lw=2.5, label=r"$\frac{d}{dt}\int \rho\, d\mu_t$")
    ax.plot(tt[::12], rh[::12], "o", color=PALETTE["red_strong"], ms=4,
            label=r"$-\int \rho\, |\vec H + x^\perp/2(t_0-t)|^2 d\mu_t$")
    ax.set_xlabel(r"$t$")
    ax.set_title("(c) the two sides of Theorem 3.1", fontsize=12)
    ax.legend(fontsize=10, loc="upper left")
    save(fig, "monotone")


# ---------------------------------------------------------------------------------------
# Figure 4: the rescaled flow
# ---------------------------------------------------------------------------------------


def fig_rescaled(hist) -> None:
    fig, axes = plt.subplots(1, 2, figsize=(10, 3.9))
    ts = np.array([t for t, _ in hist])
    s_of = lambda t: -0.5 * np.log(T - t)  # noqa: E731
    ax = axes[0]
    cmap = plt.get_cmap("Blues")
    s_snap = [s_of(0.0), 0.25, 0.5, 0.8, 1.2, s_of(ts[-1])]
    for k, s in enumerate(s_snap):
        i = min(np.searchsorted(ts, T - np.exp(-2 * s)), len(ts) - 1)
        y = hist[i][1] / np.sqrt(2 * (T - ts[i]))
        ax.plot(*np.vstack([y, y[:1]]).T, color=cmap(0.35 + 0.65 * k / (len(s_snap) - 1)), lw=2)
    th = np.linspace(0, 2 * np.pi, 200)
    ax.plot(np.cos(th), np.sin(th), color=PALETTE["red_strong"], ls="--", lw=1.8)
    ax.annotate(r"$|y| = \sqrt{n}$", (np.cos(-2.3), np.sin(-2.3)), xytext=(-1.55, -1.25), fontsize=12,
                color=PALETTE["red_strong"], arrowprops={"arrowstyle": "-", "color": PALETTE["red_strong"]})
    ax.set_aspect("equal")
    ax.set_xticks([])
    ax.set_yticks([])
    for sp in ("left", "bottom"):
        ax.spines[sp].set_visible(False)
    ax.set_title(r"(a) $\tilde F = F/\sqrt{2(T - t)}$ at $s = " + ", ".join(f"{abs(s):.2g}" if abs(s) > 0.01 else "0" for s in s_snap) + "$",
                 fontsize=11)

    ax = axes[1]
    sel = np.unique(np.searchsorted(ts, np.linspace(0, ts[-1], 300)))
    sel = sel[sel < len(ts)]
    ss, vals = [], []
    for i in sel:
        y = hist[i][1] / np.sqrt(2 * (T - ts[i]))
        ds, _, _ = geometry(y)
        vals.append(np.sum(np.exp(-np.sum(y * y, axis=1) / 2) * ds))
        ss.append(s_of(ts[i]))
    ax.plot(ss, vals, color=PALETTE["blue_main"], lw=2.5, label=r"$\int \tilde\rho\, d\tilde\mu_s$")
    ax.axhline(2 * np.pi / np.sqrt(np.e), color=PALETTE["grey"], ls="--", lw=1.5,
               label=r"unit circle: $2\pi e^{-1/2}$")
    ax.set_xlabel(r"$s = -\frac{1}{2}\log(T - t)$")
    ax.set_title("(b) the rescaled density decreases", fontsize=12)
    ax.legend(fontsize=11)
    save(fig, "rescaled")


# ---------------------------------------------------------------------------------------
# Figure 5: the shrinking sphere (circle)
# ---------------------------------------------------------------------------------------


def fig_sphere() -> None:
    fig, axes = plt.subplots(1, 2, figsize=(10, 3.7))
    Ts = 0.5  # R(t)^2 = 1 - 2t
    ax = axes[0]
    cmap = plt.get_cmap("Blues")
    th = np.linspace(0, 2 * np.pi, 300)
    tl = [0.0, 0.2, 0.35, 0.45, 0.49]
    for k, t in enumerate(tl):
        R = np.sqrt(1 - 2 * t)
        ax.plot(R * np.cos(th), R * np.sin(th), color=cmap(0.35 + 0.65 * k / (len(tl) - 1)), lw=2)
    R = 1.0
    for a in np.linspace(0, 2 * np.pi, 10, endpoint=False):
        ax.annotate("", xy=(0.72 * np.cos(a), 0.72 * np.sin(a)), xytext=(np.cos(a), np.sin(a)),
                    arrowprops={"arrowstyle": "-|>", "color": PALETTE["red_strong"], "lw": 1.5})
    ax.text(0.78, 0.92, r"$\vec H = -\frac{n}{R^2} F$", color=PALETTE["red_strong"], fontsize=12)
    ax.set_aspect("equal")
    ax.set_xticks([])
    ax.set_yticks([])
    for sp in ("left", "bottom"):
        ax.spines[sp].set_visible(False)
    ax.set_title(r"(a) $R(t) = \sqrt{1 - 2nt}$, $t = " + ", ".join(f"{t:g}" for t in tl) + "$", fontsize=11)

    ax = axes[1]
    phi = np.linspace(0, 2 * np.pi, 2000, endpoint=False)

    def theta(t, x0, t0):
        R = np.sqrt(1 - 2 * t)
        pts = np.stack([R * np.cos(phi) - x0[0], R * np.sin(phi) - x0[1]], axis=1)
        return np.mean(kernel(pts, t0 - t)) * 2 * np.pi * R

    cases = [
        ((0.0, 0.0), Ts, PALETTE["blue_main"], r"$(x_0, t_0) = (0, T)$"),
        ((0.0, 0.0), 0.7, PALETTE["teal"], r"$(0, 0.7)$"),
        ((0.4, 0.0), Ts, PALETTE["violet"], r"$((0.4, 0), T)$"),
        ((0.0, 0.0), 0.4, PALETTE["red_2"], r"$(0, 0.4)$"),
    ]
    for x0, t0, c, lab in cases:
        tt = np.linspace(0, min(t0, Ts) - 1e-3, 300)
        ax.plot(tt, [theta(t, x0, t0) for t in tt], color=c, lw=2.3, label=lab)
    ax.axvline(Ts, color=PALETTE["neutral"], lw=1)
    ax.set_xlabel(r"$t$")
    ax.set_ylabel(r"$\int \rho_{x_0, t_0}\, d\mu_t$")
    ax.set_title("(b) constant only for the right centre", fontsize=12)
    ax.legend(fontsize=10)
    save(fig, "sphere")


def main() -> None:
    fig_kernel()
    fig_sphere()
    frames, hist = run_ellipse()
    fig_integrand(frames)
    fig_monotone(frames, hist)
    fig_rescaled(hist)


if __name__ == "__main__":
    main()
