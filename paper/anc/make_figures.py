"""Generate vector figures from the formulas verified in verify_manuscript.py."""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.special import ellipj, ellipk

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "figures"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["DejaVu Serif"],
    "mathtext.fontset": "cm",
    "font.size": 10,
    "axes.labelsize": 11,
    "axes.titlesize": 10,
    "axes.linewidth": 0.7,
    "lines.linewidth": 1.6,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "savefig.bbox": "tight",
})
BLUE, ORANGE, GREEN = "#1f4e79", "#b45f06", "#38734b"


def style(ax):
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.tick_params(width=0.7, length=3)
    ax.grid(axis="y", alpha=0.16, linewidth=0.5)
    ax.set_axisbelow(True)


def save(fig, stem):
    fig.savefig(OUT / (stem + ".pdf"), metadata={"CreationDate": None, "ModDate": None})
    fig.savefig(OUT / (stem + ".png"), dpi=170)
    plt.close(fig)


def elliptic_real(g2, cycles=2):
    """X=wp(z+omega_3;g2,0), Y=X' on a bounded real translate."""
    aa = np.sqrt(g2) / 2
    frequency = np.sqrt(2 * aa)
    period = 2 * ellipk(0.5) / frequency
    z = np.linspace(0, cycles * period, 1201)
    sn, cn, dn, unused = ellipj(frequency * z, 0.5)
    xx = aa * (sn ** 2 - 1)
    yy = 2 * aa * frequency * sn * cn * dn
    np.testing.assert_allclose(yy ** 2 - 4 * xx ** 3 + g2 * xx, 0, atol=2e-15)
    return z, xx, yy, period


def axes_pair():
    return plt.subplots(1, 2, figsize=(6.4, 2.6), constrained_layout=True)


records = []
z = np.linspace(-8, 8, 1001)
q = 1 / (1 + np.exp(-z))
zp, xx, yy, period = elliptic_real(1 / 12)
fig, axes = axes_pair()
axes[0].plot(z, 12 * q * (1 - q), color=BLUE)
axes[0].set(xlabel=r"$z$", ylabel=r"$v$", title=r"KdV soliton: $P=D^2-1$", xlim=(-8, 8))
axes[1].plot(zp / period, -12 * xx + 1, color=ORANGE)
axes[1].set(xlabel=r"$z/L$", ylabel=r"$v$", title=r"KdV cnoidal wave: $P=D^2-1$", xlim=(0, 2))
for ax in axes:
    style(ax)
save(fig, "kdvb_profiles")
records.append({
    "figure": "kdvb_profiles",
    "left": {"formula": "3 sech^2(z/2)", "operator": "D^2-1"},
    "right": {"formula": "-12 X+1", "operator": "D^2-1", "g2": 1 / 12,
              "g3": 0, "real_period": float(period), "translate": "imaginary half-period"},
})

fig, axes = axes_pair()
axes[0].plot(z, 120 * q ** 3, color=BLUE)
axes[0].set(xlabel=r"$z$", ylabel=r"$v$", title=r"KS front: $v=120Q^3$", xlim=(-8, 8))
elliptic_profile = -60 * yy - 60 * xx - 1 - np.sqrt(26)
axes[1].plot(zp / period, elliptic_profile, color=ORANGE)
axes[1].set(xlabel=r"$z/L$", ylabel=r"$v$", title=r"KS elliptic wave: $g_2=1/12,\ g_3=0$", xlim=(0, 2))
for ax in axes:
    style(ax)
save(fig, "ks_profiles")
records.append({
    "figure": "ks_profiles",
    "left": {"formula": "120 Q^3", "operator": "(D-3)(D-4)(D-5)"},
    "right": {"formula": "-60 Y-60 X-1-sqrt(26)", "operator": "D^3+4D^2+D+sqrt(26)",
              "g2": 1 / 12, "g3": 0, "real_period": float(period),
              "translate": "imaginary half-period"},
})

zp4, xx4, yy4, period4 = elliptic_real(1)
fig, axes = axes_pair()
axes[0].plot(z, -105 / np.cosh(z / 2) ** 4, color=BLUE)
axes[0].set(xlabel=r"$z$", ylabel=r"$v$", title=r"Kawahara solitary wave", xlim=(-8, 8))
axes[1].plot(zp4 / period4, -1680 * xx4 ** 2 + 168 - 12 * np.sqrt(161), color=GREEN)
axes[1].set(xlabel=r"$z/L$", ylabel=r"$v$", title=r"Kawahara elliptic wave: $g_2=1,\ g_3=0$", xlim=(0, 2))
for ax in axes:
    style(ax)
save(fig, "kawahara_profiles")
records.append({
    "figure": "kawahara_profiles",
    "left": {"formula": "-105 sech^4(z/2)", "operator": "(D^2-4)(D^2-9)"},
    "right": {"formula": "-1680 X^2+168-12 sqrt(161)", "operator": "D^4+12 sqrt(161)",
              "g2": 1, "g3": 0, "real_period": float(period4),
              "translate": "imaginary half-period"},
})

report = {"figures": records, "figure_count": len(records),
          "scope": "Evaluation of exact formulas; plots are not proof or stability computations"}
(OUT / "figure_data.json").write_text(json.dumps(report, indent=2) + "\n")
print("Generated three vector PDF figures and PNG previews.")
