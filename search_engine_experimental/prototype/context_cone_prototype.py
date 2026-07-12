"""Early Context Cone Target Warping prototype supplied by the researcher.

Preserved as experimental evidence. It is not imported by production MIND.
See research/architecture.md for the audit.
"""

import math

import torch
import torch.nn as nn
import torch.nn.functional as F


class ContextCone(nn.Module):
    def __init__(self, vocab_size: int, embed_dim: int, path_dim: int = 64,
                 path_levels: int = 5, max_warp: float = 0.3, seed: int = 42):
        super().__init__()
        self.vocab_size = vocab_size
        self.embed_dim = embed_dim
        self.path_dim = path_dim
        self.path_levels = path_levels
        self.max_warp = max_warp
        self.edge_proj_dim = min(vocab_size, 128)

        rng = torch.Generator().manual_seed(seed)
        self.register_buffer(
            "edge_A",
            torch.randn(vocab_size, self.edge_proj_dim, generator=rng) / math.sqrt(self.edge_proj_dim),
        )
        self.register_buffer(
            "edge_B",
            torch.randn(vocab_size, self.edge_proj_dim, generator=rng) / math.sqrt(self.edge_proj_dim),
        )
        self.register_buffer(
            "path_dirs",
            torch.randn(path_levels, vocab_size, path_dim, generator=rng) / math.sqrt(path_dim),
        )
        phases = torch.zeros(path_levels, 1024)
        for level in range(path_levels):
            for position in range(1024):
                phases[level, position] = math.cos(
                    (position + 1) * (level + 1) * 2.3999632297286533
                )
        self.register_buffer("pos_phases", phases)

        self.fp_width = vocab_size + self.edge_proj_dim + path_dim * path_levels
        rng_proj = torch.Generator().manual_seed(seed + 999)
        projection = torch.randn(self.fp_width, embed_dim, generator=rng_proj)
        self.register_buffer("direction_proj", projection / math.sqrt(self.fp_width))

    @torch.compiler.disable
    def encode(self, token_ids):
        """Return cumulative content, edge, and n-gram path fingerprints."""
        batch, length = token_ids.shape
        device = token_ids.device

        onehot = F.one_hot(token_ids.long(), self.vocab_size).float()
        content = onehot.cumsum(dim=1)

        edges = torch.zeros(batch, length, self.edge_proj_dim, device=device)
        if length > 1:
            previous = token_ids[:, :-1].long()
            current = token_ids[:, 1:].long()
            vectors = self.edge_A[previous] * self.edge_B[current]
            edges[:, 1:] = vectors.cumsum(dim=1)

        path_parts = []
        for level in range(self.path_levels):
            n = level + 1
            accum = torch.zeros(batch, length, self.path_dim, device=device)
            if length >= n:
                for offset in range(n):
                    start = offset
                    end = length - n + 1 + offset
                    if end <= start:
                        continue
                    tokens = token_ids[:, start:end].long()
                    directions = self.path_dirs[level][tokens]
                    directions = directions * self.pos_phases[level, offset]
                    accum[:, n - 1:length, :] += directions[:, :length - n + 1, :]
                accum = accum.cumsum(dim=1)
            path_parts.append(accum)

        return torch.cat([content, edges, torch.cat(path_parts, dim=-1)], dim=-1)

    def warp(self, fingerprints):
        """Project fingerprints into the target embedding space."""
        return fingerprints @ self.direction_proj

    def forward(self, token_ids):
        return self.warp(self.encode(token_ids))
