"""Retrieval backend boundary.

Only ExactTopicBackend is active. A later search engine can implement the same
``resolve(store, detail)`` method without changing tracemap construction.
"""


class SearchBackendError(ValueError):
    pass


class ExactTopicBackend:
    name = "exact-topic-id"

    def resolve(self, store, detail):
        key = detail.strip()
        upper = key.upper()
        if upper in store.factoids:
            return {upper}, f"reference {upper}"
        topic_id = store.resolve_topic(key)
        if topic_id is None:
            raise SearchBackendError(
                f"unknown reference or topic: {detail!r}; use MIND SEARCH for similarity retrieval"
            )
        descendants = store.topic_descendants(topic_id) | {topic_id}
        matches = {
            fid
            for fid, fact in store.factoids.items()
            if descendants.intersection(fact["relates_to"])
        }
        return matches, f"topic {store.topic_path(topic_id)} [{topic_id}]"


def configured_backend(_store):
    return ExactTopicBackend()
