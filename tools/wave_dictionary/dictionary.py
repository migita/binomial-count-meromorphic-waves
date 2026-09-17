#!/usr/bin/env python3
"""Command-line dictionary; run --help for the supported input and output."""

import argparse
import json
from pathlib import Path
import sys

import sympy as s

from core import (UnsupportedReduction, elliptic_profile, identify, parse,
                  reduce_pde, riccati_profile, serializable, solve_univariate)


HERE = Path(__file__).resolve().parent


def models():
    return {row["id"]: row for row in json.loads((HERE/"models.json").read_text())}


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    sub = result.add_subparsers(dest="command", required=True)
    listing = sub.add_parser("models", help="List the explicit model presets.")
    listing.add_argument("--json", action="store_true")
    catalogue = sub.add_parser("catalogue", help="Print the reference list of real unit-rate pairs for p<=4.")
    catalogue.add_argument("--order", type=int, choices=(1, 2, 3, 4), required=True)
    catalogue.add_argument("--json", action="store_true")
    waves = sub.add_parser("waves", help="Construct exact one-pole profiles and all their parameter conditions.")
    choice = waves.add_mutually_exclusive_group(required=True)
    choice.add_argument("--model", choices=list(models()))
    choice.add_argument("--linear", help="L in L u + M(u**2/2)=0; derivative symbols Dt,Dx,Dy,Dz.")
    waves.add_argument("--quadratic", help="M, required with --linear.")
    waves.add_argument("--speed", default="c", help="Speed in xi=kx*x+ky*y+kz*z-c*t.")
    waves.add_argument("--direction", nargs=3, metavar=("KX", "KY", "KZ"))
    waves.add_argument("--set", action="append", default=[], metavar="NAME=VALUE", help="Specify a coefficient; repeat as needed.")
    waves.add_argument("--kind", choices=("exponential", "rational", "elliptic", "all"), default="all")
    waves.add_argument("--rate", default="kappa", help="Nonzero exponential rate, possibly complex.")
    waves.add_argument("--g2", default="g2")
    waves.add_argument("--g3", default="g3")
    waves.add_argument("--background", help="Prescribe U at E=0 (exponential), infinity (rational), or an equilibrium (elliptic).")
    waves.add_argument("--solve", metavar="VARIABLE", help="Isolate all roots if the remaining conditions are univariate over Q.")
    waves.add_argument("--max-order", type=int, default=8, help="Computation limit; default 8, may be raised explicitly.")
    waves.add_argument("--json", action="store_true")
    lookup = sub.add_parser("identify", help="Normalize a rational expression in E=exp(z) and identify its pair.")
    lookup.add_argument("expression", help="For example: '12*E/(1+E)**2'.")
    lookup.add_argument("--json", action="store_true")
    return result


def print_result(data):
    if "reduction" not in data:
        for key, value in data.items():
            print("%s: %s" % (key, value))
        return
    red = data["reduction"]
    print("Equation: (%s) u + (%s) (u**2/2) = 0" % (red["linear_pde"], red["quadratic_pde"]))
    print("Phase: xi = %s*x + %s*y + %s*z - (%s)*t" % (*red["direction"], red["speed"]))
    print("Autonomous profile: (%s) U + (%s)*U**2/2 + K = 0" % (red["L"], red["q"]))
    print("P(D) about B: %s; v = (%s)*(U-B)" % (red["P_about_B"], red["v_scale"]))
    print("Equilibrium background: %s = 0" % red["background_equation"])
    print("Integrations: %s; K %s; profile order: %s" %
          (red["integrations"], "is free" if red["integrations"] else "= 0", red["order"]))
    if red["integrations"] >= 2:
        print("Scope: polynomial forcing from the integrations is set to zero.")
    print("Classification applies to all meromorphic profiles in this branch: %s" % red["meromorphic_classification_applies"])
    print("All profiles allow an arbitrary translation of xi; conditions are simultaneous, guards are nonzero.")
    for wave in data["waves"]:
        print("\n%s: %s" % (wave["kind"], wave["status"]))
        if "reason" in wave:
            print(wave["reason"])
            continue
        print(wave["coordinate_definition"])
        if "rate" in wave:
            print("kappa = %s; %s" % (wave["rate"], wave["Q_definition"]))
        if "g2" in wave:
            print("g2 = %s; g3 = %s" % (wave["g2"], wave["g3"]))
        print("U = %s" % wave["profile"])
        if "profile_in_Q" in wave:
            print("U in Q = %s" % wave["profile_in_Q"])
        print("Conditions: %s" % ("; ".join("%s = 0" % e for e in wave["conditions"]) or "none"))
        print("Guards: %s" % ("; ".join("%s != 0" % g for g in wave["guards"]) or "none"))
        print("K = %s" % wave["integration_constant"])
        if "solution" in wave:
            print("Parameter solution: %s" % serializable(wave["solution"]))


def main(argv=None):
    args = parser().parse_args(argv)
    try:
        if args.command == "models":
            data = list(models().values())
            if args.json:
                print(json.dumps(data, indent=2, ensure_ascii=False))
            else:
                for row in data:
                    print("%s: %s\n  L = %s; M = %s" % (row["id"], row["name"], row["linear"], row["quadratic"]))
            return 0
        if args.command == "catalogue":
            data = json.loads((HERE/"real_pairs_p1_p4.json").read_text())[str(args.order)]
            if args.json:
                print(json.dumps(data, indent=2))
            else:
                print("%s real unit-rate pairs at p=%s; the constructor also handles complex pairs." % (len(data), args.order))
                for row in data:
                    print("\nA = %s\nP = %s\nv = %s" % (row["A"], row["P_factored"], row["profile"]))
            return 0
        if args.command == "identify":
            data = identify(parse(args.expression))
        else:
            substitutions = {}
            for item in args.set:
                name, separator, value = item.partition("=")
                if not separator or not name.isidentifier() or name in ("Dt", "Dx", "Dy", "Dz", "I"):
                    raise ValueError("--set requires a parameter NAME=VALUE.")
                substitutions[s.Symbol(name)] = parse(value)
            def expression(text):
                value = parse(text).subs(substitutions, simultaneous=True)
                if value.has(s.zoo, s.nan, s.oo, -s.oo):
                    raise ValueError("Parameter substitution produced a nonfinite coefficient.")
                return value
            if args.model:
                row = models()[args.model]
                linear, quadratic = expression(row["linear"]), expression(row["quadratic"])
                direction = args.direction or row["direction"]
            else:
                if args.quadratic is None:
                    raise ValueError("--quadratic is required with --linear.")
                linear, quadratic = expression(args.linear), expression(args.quadratic)
                direction = args.direction or ["1", "0", "0"]
            red = reduce_pde(linear, quadratic, expression(args.speed),
                             tuple(expression(k) for k in direction), max_order=args.max_order)
            waves = []
            background = None if args.background is None else expression(args.background)
            for kind in ("exponential", "rational", "elliptic") if args.kind == "all" else [args.kind]:
                if kind == "elliptic":
                    wave = elliptic_profile(red, expression(args.g2), expression(args.g3), background)
                else:
                    wave = riccati_profile(red, kind, expression(args.rate), background)
                if args.solve:
                    wave["solution"] = solve_univariate(wave, parse(args.solve))
                waves.append(wave)
            data = {"reduction": red, "waves": waves}
        if args.json:
            print(json.dumps(serializable(data), indent=2, ensure_ascii=False))
        else:
            print_result(data)
        return 0
    except (ValueError, s.PolynomialError) as exc:
        data = {"status": "unsupported" if isinstance(exc, UnsupportedReduction) else "input_error", "reason": str(exc)}
        if args.json:
            print(json.dumps(data, indent=2))
        else:
            print("%s: %s" % (data["status"], data["reason"]), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
