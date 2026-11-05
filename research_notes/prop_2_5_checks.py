"""Independent symbolic checks of the claims in PROPOSITION_2_5_AUDIT.md.

Run with:  python3 -I research_notes/prop_2_5_checks.py   (needs sympy)

Setting: the cone C(S^1_{2 pi beta}) x R with metric g = dr^2 + beta^2 r^2 dtheta^2 + ds^2,
in the paper's normalisation (Delta_g = div grad, -Delta v = lambda v).  Everything below is a
symbolic identity or an exact integral; each check prints OK or raises AssertionError.
"""

import sympy as sp

r, th, s, R, beta, eps = sp.symbols("r theta s R beta epsilon", positive=True)
coords = (r, th, s)
g = sp.diag(1, beta**2 * r**2, 1)
ginv = g.inv()
sqrtg = beta * r  # sqrt(det g)


def christoffel(g, ginv):
    n = len(coords)
    return [[[sp.simplify(sum(ginv[k, l] * (sp.diff(g[l, i], coords[j]) + sp.diff(g[l, j], coords[i])
                                              - sp.diff(g[i, j], coords[l])) for l in range(n)) / 2)
              for j in range(n)] for i in range(n)] for k in range(n)]


Gam = christoffel(g, ginv)


def grad(u):
    return [sum(ginv[i, j] * sp.diff(u, coords[j]) for j in range(3)) for i in range(3)]


def inner_grad(u, w):
    return sum(ginv[i, j] * sp.diff(u, coords[i]) * sp.diff(w, coords[j]) for i in range(3) for j in range(3))


def lap(u):
    return sp.simplify(sum(sp.diff(sqrtg * sum(ginv[i, j] * sp.diff(u, coords[j]) for j in range(3)), coords[i])
                           for i in range(3)) / sqrtg)


def hess(u):
    return sp.Matrix(3, 3, lambda i, j: sp.diff(u, coords[i], coords[j])
                     - sum(Gam[k][i][j] * sp.diff(u, coords[k]) for k in range(3)))


def hess_norm_sq(u):
    H = hess(u)
    return sp.simplify(sum(ginv[i, k] * ginv[j, l] * H[i, j] * H[k, l]
                           for i in range(3) for j in range(3) for k in range(3) for l in range(3)))


def div(V):  # V given by its components in the coordinate frame
    return sum(sp.diff(sqrtg * V[i], coords[i]) for i in range(3)) / sqrtg


def check(name, expr):
    assert sp.simplify(expr) == 0, f"{name}: {sp.simplify(expr)}"
    print(f"OK  {name}")


# --- Christoffel symbols of the cone factor -------------------------------------------------
check("Gamma^r_{theta theta} = -beta^2 r", Gam[0][1][1] + beta**2 * r)
check("Gamma^theta_{r theta} = 1/r", Gam[1][0][1] - 1 / r)

# --- 1. Bochner identity on the regular part (Ric = 0) ----------------------------------------
v = sp.Function("v")(r, th, s)
F = -lap(v)
bochner = sp.Rational(1, 2) * lap(inner_grad(v, v)) - hess_norm_sq(v) + inner_grad(v, F)
check("Bochner: 1/2 Delta|grad v|^2 = |Hess v|^2 - <grad v, grad F>,  F = -Delta v",
      sp.expand(bochner))

# --- 2. Radial Dirichlet eigenfunction on B_1 = {R < 1}, m = 3 -------------------------------
vr = sp.sin(sp.pi * R) / R
d1, d2 = sp.diff(vr, R), sp.diff(vr, R, 2)
check("radial Laplacian: v'' + 2v'/R = -pi^2 v", d2 + 2 * d1 / R + sp.pi**2 * vr)
assert sp.limit(vr, R, 0) == sp.pi and vr.subs(R, 1) == 0
print("OK  v(0) = pi, v(1) = 0 (Dirichlet)")
# Integrals of radial functions: dV_g = beta * (Euclidean R^3 volume) = beta * 4 pi R^2 dR.
I_v2 = 4 * sp.pi * beta * sp.integrate(sp.expand(R**2 * vr**2), (R, 0, 1))
check("int_{B_1} v^2 dV_g = 2 pi beta", I_v2 - 2 * sp.pi * beta)
I_lap2 = sp.pi**4 * I_v2
check("int_{B_1} (Delta v)^2 dV_g = 2 pi^5 beta", I_lap2 - 2 * sp.pi**5 * beta)
# |Hess v|^2 for a radial function on a 3-dim metric cone: v''^2 + 2 (v'/R)^2.
I_hess = 4 * sp.pi * beta * sp.integrate(sp.simplify((d2**2 + 2 * (d1 / R) ** 2) * R**2), (R, 0, 1))
check("int_{B_1} |Hess v|^2 dV_g = 2 pi^3 beta (pi^2 - 4)", I_hess - 2 * sp.pi**3 * beta * (sp.pi**2 - 4))
check("v'(1) = -pi", d1.subs(R, 1) + sp.pi)
area = 4 * sp.pi * beta  # |dB_1| = beta * 4 pi (induced metric dpsi^2 + beta^2 sin^2 psi dtheta^2)
bdry = (3 - 1) * area * d1.subs(R, 1) ** 2
check("(m-1) int_{dB_1} (dv/dnu)^2 dA = 8 pi^3 beta", bdry - 8 * sp.pi**3 * beta)
check("boundary identity (2.2): int|Hess|^2 = lambda^2 int v^2 - (m-1) int (dv/dnu)^2",
      I_hess - (I_lap2 - bdry))
assert sp.simplify(I_hess - I_lap2) != 0
print("OK  the claimed equality int|Hess v|^2 = int (Delta v)^2 FAILS (difference = -8 pi^3 beta)")
# Hessian of a radial function on the cone, checked against the general formula.
Rexpr = sp.sqrt(r**2 + s**2)
vcone = sp.sin(sp.pi * Rexpr) / Rexpr
hv = hess_norm_sq(vcone)
target = (d2**2 + 2 * (d1 / R) ** 2).subs(R, Rexpr)
check("|Hess v|^2 = v''^2 + 2 (v'/R)^2 for the radial function on the cone", hv - target)
check("Delta_g v = -pi^2 v on the cone (in (r, theta, s))", lap(vcone) + sp.pi**2 * vcone)

# --- 3. u = x = r cos(theta): Euclidean Hessian 0, intrinsic Hessian not in L^2 ---------------
u = r * sp.cos(th)
H = hess(u)
check("Hess u (theta, theta) = (beta^2 - 1) r cos(theta)", H[1, 1] - (beta**2 - 1) * r * sp.cos(th))
check("Hess u in the frame e_theta = (beta r)^-1 d_theta: (beta^2-1) cos(theta) / (beta^2 r)",
      H[1, 1] / (beta * r) ** 2 - (beta**2 - 1) * sp.cos(th) / (beta**2 * r))
check("Hess u (r, theta) = 0 and Hess u (r, r) = 0", H[0, 1] ** 2 + H[0, 0] ** 2)
hn = hess_norm_sq(u)
check("|Hess u|^2 = (beta^2-1)^2 cos^2(theta) / (beta^4 r^2)",
      hn - (beta**2 - 1) ** 2 * sp.cos(th) ** 2 / (beta**4 * r**2))
I_eps = sp.integrate(sp.integrate(hn * sqrtg, (th, 0, 2 * sp.pi)), (r, eps, sp.Rational(1, 2)))
check("int_{eps < r < 1/2} |Hess u|^2 dV_g (per unit s-length) = pi (1-beta^2)^2/beta^3 log(1/(2 eps))",
      sp.simplify(I_eps - sp.pi * (1 - beta**2) ** 2 / beta**3 * sp.log(1 / (2 * eps))))
print("    -> diverges as eps -> 0 for beta != 1: u is in Euclidean W^{2,2} but Hess_g u is not in L^2")
check("Delta_g u = (1 - 1/beta^2) cos(theta) / r (not in L^2 near the axis)",
      lap(u) - (1 - 1 / beta**2) * sp.cos(th) / r)

# --- 4. Localised Bochner identity (5.1) as a divergence identity ----------------------------
eta = sp.Function("eta")(r, th, s)
w = inner_grad(v, v)
eta2 = eta**2
integrand_lhs = eta2 * hess_norm_sq(v)
integrand_rhs = (eta2 * F**2 - 2 * eta * F * inner_grad(eta, v)
                 + sp.Rational(1, 2) * lap(eta2) * w)
gv, gw, ge2 = grad(v), grad(w), grad(eta2)
W = [sp.Rational(1, 2) * (eta2 * gw[i] - w * ge2[i]) + eta2 * F * gv[i] for i in range(3)]
check("(5.1) integrand difference is div_g W with "
      "W = 1/2 (eta^2 grad|grad v|^2 - |grad v|^2 grad eta^2) + eta^2 F grad v",
      sp.expand(integrand_lhs - integrand_rhs - div(W)))

# --- 5. D_2 operators versus components of the intrinsic Hessian -----------------------------
Hu = hess(v)
e_r_e_r = Hu[0, 0]
e_r_e_th = Hu[0, 1] / (beta * r)
e_th_e_th = Hu[1, 1] / (beta * r) ** 2
e_th_s = Hu[1, 2] / (beta * r)
d = sp.diff
check("d^2_r v = Hess(e_r, e_r)", d(v, r, 2) - e_r_e_r)
check("d^2_{r s} v = Hess(e_r, d_s)", d(v, r, s) - Hu[0, 2])
check("r^-1 d^2_{theta s} v = beta Hess(e_theta, d_s)", d(v, th, s) / r - beta * e_th_s)
check("Delta_beta v + d^2_s v = trace Hess v", lap(v) - (e_r_e_r + e_th_e_th + Hu[2, 2]))
check("r^-2 d^2_theta v = beta^2 Hess(e_theta, e_theta) - beta^2 r^-1 d_r v",
      d(v, th, 2) / r**2 - (beta**2 * e_th_e_th - beta**2 * d(v, r) / r))
check("r^-1 d^2_{r theta} v = beta Hess(e_r, e_theta) + r^-2 d_theta v",
      d(v, r, th) / r - (beta * e_r_e_th + d(v, th) / r**2))

print("\nAll checks passed.")
