"""Exploratory floating-point search, never a proof or exact certificate."""
import itertools
import json
from pathlib import Path
import numpy as np

rng = np.random.default_rng(50420261020)
records = []
for size in range(3, 11):
    pts = rng.normal(size=(24000, size, 2))
    # Anisotropy and hierarchical pairs supplement generic configurations.
    pts[:8000, :, 1] *= rng.uniform(.05, 1, (8000, 1))
    pts[8000:16000, size//2:] = pts[8000:16000, :size-size//2] + .01*pts[8000:16000, size//2:]
    vec = pts[:, None, :, :] - pts[:, :, None, :]
    norms = np.linalg.norm(vec, axis=-1)
    safe = np.where(norms > 0, norms, 1)
    unit = vec / safe[..., None]
    cosine = np.einsum('bijc,bikc->bijk', unit, unit)
    trip = np.array(list(itertools.permutations(range(size), 3)))
    min_cos = cosine[:, trip[:, 0], trip[:, 1], trip[:, 2]].min(axis=1)
    directions = np.mod(np.arctan2(vec[..., 1], vec[..., 0]), np.pi)
    directions[:, np.arange(size), np.arange(size)] = np.inf
    directions.sort(axis=2)
    angles = directions[:, :, :size-1]
    gaps = np.diff(np.concatenate((angles, angles[:, :, :1]+np.pi),axis=2), axis=2)/np.pi
    for t in [2.49,2.99,3.49,3.99,4.49,4.99,5.49,5.99]:
        valid = min_cos > np.cos(np.pi*(1-1/t)) + 1e-8
        exponent = np.maximum(np.floor(t*gaps+1e-10)-1,0).sum(axis=2).astype(int)
        weight = (2**exponent).sum(axis=1)
        m=int(t)
        bound = 2**m if t-m < .5 else 2**m+2**(m-2)
        if valid.any():
            best=int(np.argmax(np.where(valid,weight,-1)))
            records.append(dict(size=size,t=t,bound=bound,valid=int(valid.sum()),
                max_weight=int(weight[best]),exponents=exponent[best].tolist(),
                points=pts[best].tolist(),min_cos=float(min_cos[best]),
                angle_margin=float(min_cos[best]-np.cos(np.pi*(1-1/t)))))
            print(size,t,'valid',int(valid.sum()),'best',int(weight[best]),'bound',bound,flush=True)
out=Path(__file__).with_name('random-probe.json')
out.write_text(json.dumps(dict(seed=50420261020,per_size=24000,
    evidence='Floating-point exploration only. Not exhaustive; no theorem or counterexample certified.',
    records=records),indent=2)+'\n')
