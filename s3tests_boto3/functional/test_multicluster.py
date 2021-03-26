import boto3
import botocore.session
from botocore.exceptions import ClientError
from botocore.exceptions import ParamValidationError
from nose.tools import eq_ as eq
from nose.plugins.attrib import attr
from nose.plugins.skip import SkipTest
import isodate
import email.utils
import datetime
import threading
import re
import pytz
from collections import OrderedDict
import requests
import json
import base64
import hmac
import hashlib
import xml.etree.ElementTree as ET
import time
import operator
import nose
import os
import string
import random
import socket
import dateutil.parser
import ssl
from collections import namedtuple
from time import sleep

from email.header import decode_header

from .utils import assert_raises
from .utils import generate_random
from .utils import _get_status_and_error_code
from .utils import _get_status

from .policy import Policy, Statement, make_json_policy

from . import (
    get_client,
    get_new_bucket_resource,
    get_same_bucket_resource,
    get_new_bucket_name
    )


def migrate():
    sleep(1)

def _create_bucket_with_objects(bucket=None, bucket_name=None, keys=[], use_second=None):
    """
    Populate a (new or specified) bucket with objects with
    specified names (and contents identical to their names).
    """
    if bucket_name is None:
        bucket_name = get_new_bucket_name()

    if bucket is None:
        bucket = get_new_bucket_resource(name=bucket_name, use_second=use_second)

    for key in keys:
        obj = bucket.put_object(Body=key, Key=key)

    return bucket_name

def _get_keys(response):
    """
    return lists of strings that are the keys from a client.list_objects() response
    """
    keys = []
    if 'Contents' in response:
        objects_list = response['Contents']
        keys = [obj['Key'] for obj in objects_list]
    return keys
    
def _bucket_is_empty(bucket):
    is_empty = True
    for obj in bucket.objects.all():
        is_empty = False
        break
    return is_empty

# def test_connections():
#     cluster1 = get_client()
#     cluster2 = get_client(use_second=True)

@attr(resource='bucket')
@attr(method='get')
@attr(operation='list')
@attr(assertion='empty buckets return no contents')
def test_bucket_list_empty():
    """
    Tests the connection to both clusters 
    And also that both buckets are currently empty
    (clean test state)
    """
    bucket = get_new_bucket_resource()
    is_empty = _bucket_is_empty(bucket)
    eq(is_empty, True)
    bucket2 = get_new_bucket_resource(use_second=True)
    is_empty = _bucket_is_empty(bucket2)
    eq(is_empty, True)

@attr('multicluster')
@attr(resource='bucket')
@attr(method='get')
@attr(operation='list')
@attr(assertion='distinct buckets have different contents')
def test_bucket_list_distinct():
    """
    Migrates buckets to the second cluster and tests contents
    Small buckets, no ACL checks
    """
    bucket1 = get_new_bucket_resource()
    bucket2 = get_new_bucket_resource()
    obj = bucket1.put_object(Body='str', Key='asdf')
    is_empty = _bucket_is_empty(bucket2)
    eq(is_empty, True)

    migrate()

    bucket1_2 = get_same_bucket_resource(bucket1, use_second=True)
    bucket2_2 = get_same_bucket_resource(bucket2, use_second=True)
    eq(bucket1, bucket1_2)
    is_empty = _bucket_is_empty(bucket2_2)
    eq(is_empty, True)

@attr(resource='bucket')
@attr(method='get')
@attr(operation='list all keys')
@attr(assertion='pagination w/max_keys=2, no marker')
def test_bucket_list_many():
    """
    Tests pagination of object retrieval on both clusters
    Creates a number of buckets and retrieves with pagination set to 2
    """
    bucket_name = _create_bucket_with_objects(keys=['foo', 'bar', 'baz'])

    client1 = get_client()

    response = client1.list_objects(Bucket=bucket_name, MaxKeys=2)
    keys = _get_keys(response)
    eq(len(keys), 2)
    eq(keys, ['bar', 'baz'])
    eq(response['IsTruncated'], True)

    response = client1.list_objects(Bucket=bucket_name, Marker='baz',MaxKeys=2)
    keys = _get_keys(response)
    eq(len(keys), 1)
    eq(response['IsTruncated'], False)
    eq(keys, ['foo'])

    migrate()

    client2 = get_client(use_second=True)
    response = client2.list_objects(Bucket=bucket_name, MaxKeys=2)
    keys = _get_keys(response)
    eq(len(keys), 2)
    eq(keys, ['bar', 'baz'])
    eq(response['IsTruncated'], True)

    response = client2.list_objects(Bucket=bucket_name, Marker='baz',MaxKeys=2)
    keys = _get_keys(response)
    eq(len(keys), 1)
    eq(response['IsTruncated'], False)
    eq(keys, ['foo'])