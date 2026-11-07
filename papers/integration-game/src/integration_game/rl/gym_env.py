"""
Gymnasium adapters for Integration Game offline synthesis and online mediation.

Requires optional extra: pip install 'integration-game[rl]'  (gymnasium, numpy)

Stable Discrete(A_max) layout (MaskablePPO-ready):
  - indices [0, n_catalog): add catalog[i] when unused / legal
  - indices [n_catalog, A_max-1): connect actions hashed into bounded slots
  - index A_max-1: finalize

Observation Dict:
  obs: float32 Box(len(OBS_KEYS),)
  action_mask: bool MultiBinary(A_max)
"""
from __future__ import annotations

import hashlib
from typing import Any, Callable, Dict, List, Optional, Tuple

import numpy as np

from integration_game.rl.env import (
    OBS_KEYS,
    TASK_NAME_TO_FACTORY,
    IntegrationGameEnv,
    SynthTask,
    make_ping_pong_task,
)
from integration_game.rl.online_env import OnlineMediationEnv

try:
    import gymnasium as gym
    from gymnasium import spaces
except ImportError as exc:  # pragma: no cover
    raise ImportError(
        "integration_game.rl.gym_env requires gymnasium. "
        "Install with: pip install 'integration-game[rl]'"
    ) from exc


def _stable_connect_slot(src: str, tgt: str, n_catalog: int, connect_budget: int) -> int:
    """Map a route pair into a stable connect slot in [n_catalog, n_catalog+connect_budget)."""
    if connect_budget <= 0:
        raise ValueError("max_actions too small for catalog size")
    digest = hashlib.blake2b(f"{src}|{tgt}".encode(), digest_size=8).digest()
    h = int.from_bytes(digest, "little")
    return n_catalog + (h % connect_budget)


class IntegrationGameGymEnv(gym.Env):
    """Gymnasium wrapper around IntegrationGameEnv with action masks."""

    metadata = {"render_modes": []}

    def __init__(
        self,
        task: Optional[SynthTask] = None,
        task_name: str = "ex02",
        max_actions: int = 64,
        illegal_penalty: float = -1.0,
        raise_on_illegal: bool = False,
        **env_kwargs: Any,
    ):
        super().__init__()
        if task is None:
            factory = TASK_NAME_TO_FACTORY.get(task_name)
            if factory is None:
                raise KeyError(f"Unknown task_name {task_name!r}")
            task = factory()
        self.core = IntegrationGameEnv(task, raise_on_illegal=raise_on_illegal, **env_kwargs)
        self.max_actions = int(max_actions)
        self.illegal_penalty = float(illegal_penalty)
        self.n_catalog = len(task.catalog)
        if self.max_actions < self.n_catalog + 1:
            raise ValueError(
                f"max_actions={self.max_actions} must be >= n_catalog+1={self.n_catalog + 1}"
            )
        self.finalize_idx = self.max_actions - 1
        self.connect_budget = self.max_actions - self.n_catalog - 1
        self._catalog_names = [name for name, _ in task.catalog]
        self._name_to_add_idx = {n: i for i, n in enumerate(self._catalog_names)}

        # Finite bounds avoid gymnasium env_checker infinity warnings; values are soft.
        self.observation_space = spaces.Dict(
            {
                "obs": spaces.Box(
                    low=-1.0e6, high=1.0e6, shape=(len(OBS_KEYS),), dtype=np.float32
                ),
                "action_mask": spaces.MultiBinary(self.max_actions),
            }
        )
        self.action_space = spaces.Discrete(self.max_actions)

    def _obs_vec(self, obs_dict: Dict[str, float]) -> np.ndarray:
        return np.asarray([float(obs_dict[k]) for k in OBS_KEYS], dtype=np.float32)

    def _slot_for_move(self, kind: str, payload: Any) -> Optional[int]:
        if kind == "add":
            return self._name_to_add_idx.get(payload)
        if kind == "finalize":
            return self.finalize_idx
        if kind == "connect":
            src, tgt = payload
            return _stable_connect_slot(src, tgt, self.n_catalog, self.connect_budget)
        return None

    def _build_mask_and_decode(
        self, legal: List[Tuple[str, Any]]
    ) -> Tuple[np.ndarray, Dict[int, Tuple[str, Any]]]:
        mask = np.zeros(self.max_actions, dtype=np.int8)
        decode: Dict[int, Tuple[str, Any]] = {}
        # Deterministic collision resolution: lexicographic smaller signature wins
        candidates: Dict[int, List[Tuple[str, Any]]] = {}
        for kind, payload in legal:
            slot = self._slot_for_move(kind, payload)
            if slot is None or slot < 0 or slot >= self.max_actions:
                continue
            candidates.setdefault(slot, []).append((kind, payload))
        for slot, moves in candidates.items():
            moves.sort(key=lambda kp: self.core.action_signature(kp[0], kp[1]))
            decode[slot] = moves[0]
            mask[slot] = 1
        return mask, decode

    def _pack(self, obs_dict: Dict[str, float]) -> Dict[str, np.ndarray]:
        legal = self.core.legal_moves() if self.core.play is not None else []
        mask, decode = self._build_mask_and_decode(legal)
        self._decode = decode
        return {"obs": self._obs_vec(obs_dict), "action_mask": mask}

    def reset(self, *, seed: Optional[int] = None, options: Optional[dict] = None):
        super().reset(seed=seed)
        obs_dict = self.core.reset(seed=seed)
        obs = self._pack(obs_dict)
        info = {"n_legal": int(obs["action_mask"].sum()), "task": self.core.task.name}
        return obs, info

    def step(self, action: int):
        action = int(action)
        mask, decode = self._build_mask_and_decode(self.core.legal_moves())
        self._decode = decode

        if action < 0 or action >= self.max_actions or mask[action] == 0:
            # Illegal / masked-off: penalty + no-op (never clamp to a different legal move)
            if self.core.raise_on_illegal:
                raise ValueError(f"Illegal or masked action {action}")
            obs_dict = self.core.observe()
            self.core.moves_taken += 1
            truncated = self.core.moves_taken >= self.core.task.max_moves
            obs = self._pack(obs_dict)
            info = {
                "illegal": True,
                "terminal_reason": "max_moves" if truncated else None,
                "action_mask": mask,
            }
            return obs, self.illegal_penalty, False, truncated, info

        kind, payload = decode[action]
        result = self.core.step_move(kind, payload)
        terminated = bool(result.info.get("terminated", False))
        truncated = bool(result.info.get("truncated", False))
        if result.done and not terminated and not truncated:
            # Fallback: treat remaining done as terminated
            terminated = True
        obs = self._pack(result.obs)
        info = {
            k: v
            for k, v in result.info.items()
            if k != "score"
        }
        info["action_mask"] = mask
        if "score" in result.info:
            score = result.info["score"]
            info["fitness_S"] = float(score.fitness_score_S)
            info["win"] = bool(score.is_winning_play)
        return obs, float(result.reward), terminated, truncated, info


class OnlineMediationGymEnv(gym.Env):
    """Gymnasium wrapper for OnlineMediationEnv (Discrete{0,1} mux control)."""

    metadata = {"render_modes": []}

    def __init__(self, **kwargs: Any):
        super().__init__()
        self.core = OnlineMediationEnv(**kwargs)
        self.observation_space = spaces.Box(
            low=0.0, high=1.0, shape=(4,), dtype=np.float32
        )
        self.action_space = spaces.Discrete(2)
        self._rng = np.random.default_rng()

    def _vec(self, obs: Dict[str, float]) -> np.ndarray:
        return np.asarray(
            [
                obs["primary_ok"],
                obs["consecutive_drops"],
                obs["current_idx"],
                obs["breached"],
            ],
            dtype=np.float32,
        )

    def reset(self, *, seed: Optional[int] = None, options: Optional[dict] = None):
        super().reset(seed=seed)
        import random as _random

        rng = _random.Random(seed) if seed is not None else _random.Random()
        dropout_window = None
        if options and "dropout_window" in options:
            dropout_window = options["dropout_window"]
        obs = self.core.reset(rng=rng, dropout_window=dropout_window)
        return self._vec(obs), {}

    def step(self, action: int):
        obs, reward, done, info = self.core.step(int(action))
        terminated = bool(done)
        truncated = False
        return self._vec(obs), float(reward), terminated, truncated, info


def make_offline_gym_env(
    task_name: str = "ex02",
    max_actions: int = 64,
    **kwargs: Any,
) -> IntegrationGameGymEnv:
    """Factory for MaskablePPO-ready offline synthesis env."""
    return IntegrationGameGymEnv(task_name=task_name, max_actions=max_actions, **kwargs)


def make_online_gym_env(**kwargs: Any) -> OnlineMediationGymEnv:
    return OnlineMediationGymEnv(**kwargs)
