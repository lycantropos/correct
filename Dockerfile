ARG IMAGE_NAME
ARG IMAGE_VERSION

FROM ${IMAGE_NAME}:${IMAGE_VERSION}

RUN pip install --upgrade pip setuptools

WORKDIR /opt/correct

COPY requirements.txt .
RUN pip install -r requirements.txt

COPY requirements-tests.txt .
RUN pip install -r requirements-tests.txt

COPY README.md .
COPY pytest.ini .
COPY setup.py .
COPY correct correct
COPY tests tests
