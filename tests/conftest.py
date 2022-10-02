import os
from datetime import timedelta
from typing import TypeVar

import pytest
from hypothesis import settings

from correct._core.utils import annotation_repr

on_ci = bool(os.getenv('CI', False))
max_examples = settings.default.max_examples
settings.register_profile('default',
                          deadline=(timedelta(hours=1) / max_examples
                                    if on_ci
                                    else None),
                          max_examples=max_examples)


@pytest.fixture(scope='session',
                autouse=True)
def setup_repr() -> None:
    TypeVar.__repr__ = annotation_repr.dispatch(TypeVar)


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session: pytest.Session,
                         exitstatus: pytest.ExitCode) -> None:
    if exitstatus == pytest.ExitCode.NO_TESTS_COLLECTED:
        session.exitstatus = pytest.ExitCode.OK
