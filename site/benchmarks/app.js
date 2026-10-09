"use strict";

(() => {
  const byId = (id) => document.getElementById(id);
  const results = byId("results");
  const filters = byId("filters");
  const programFilter = byId("program-filter");
  const machineFilter = byId("machine-filter");
  const threadFilter = byId("thread-filter");
  const sortOrder = byId("sort-order");
  const categoryBrowser = byId("category-browser");
  const categories = {
    client: { name: "Client-side proving", description: "On-device measurements, Falcon signature verification and L1 state proofs." },
    consensus: { name: "Consensus layer", description: "leanXMSS, leanSPHINCS and aggregation workloads, excluding on-device results." },
    data: { name: "Data layer", description: "leanDA workloads." },
    misc: { name: "Misc", description: "Other workloads, kept together until they find a home." },
    all: { name: "All benchmarks", description: "Every published configuration, grouped by use case." },
  };
  let selectedCategory = "client";
  const numberFormat = new Intl.NumberFormat("en", { maximumFractionDigits: 6 });
  const dateFormat = new Intl.DateTimeFormat("en", {
    year: "numeric", month: "short", day: "numeric", timeZone: "UTC",
  });
  let measurements = [];

  function element(tag, className, text) {
    const node = document.createElement(tag);
    if (className) node.className = className;
    if (text !== undefined) node.textContent = text;
    return node;
  }

  function text(value, fallback = "Not recorded") {
    return typeof value === "string" && value.trim() ? value : fallback;
  }

  function safeUrl(value) {
    if (typeof value !== "string" || !value.trim()) return null;
    try {
      const url = new URL(value);
      return ["https:", "http:"].includes(url.protocol) ? url.href : null;
    } catch {
      return null;
    }
  }

  function link(label, url, className) {
    const href = safeUrl(url);
    const node = element(href ? "a" : "span", className, label);
    if (href) {
      node.href = href;
      node.rel = "noopener noreferrer";
    }
    return node;
  }

  function timestamp(value) {
    if (typeof value !== "string" || !value.trim()) return null;
    const time = Date.parse(value);
    return Number.isFinite(time) ? time : null;
  }

  function dateNode(value, className, fallback) {
    const time = timestamp(value);
    if (time === null) return element("span", className, fallback);
    const node = element("time", className, dateFormat.format(time));
    node.dateTime = new Date(time).toISOString();
    node.title = `${new Date(time).toISOString()} (UTC)`;
    return node;
  }

  function seconds(value) {
    return value > 0 && value < 0.000001 ? value.toExponential(3) : numberFormat.format(value);
  }

  function threadLabel(row) {
    const count = row.threads?.count;
    return Number.isInteger(count) && count > 0
      ? `${count} ${count === 1 ? "thread" : "threads"}`
      : text(row.threads?.label, "Default (not recorded)");
  }

  function threadKey(row) {
    const count = row.threads?.count;
    return Number.isInteger(count) && count > 0 ? `count:${count}` : `label:${threadLabel(row)}`;
  }

  function categoryOf(row) {
    if (/^leanda\b/i.test(row.program.name)) return "data";
    if (/pixel|iphone/i.test(text(row.machine.name, row.machine.id))
      || /^falcon\b/i.test(row.program.name) || /^L1 state proofs$/i.test(row.program.name)) return "client";
    if (/^lean(?:xmss|sphincs)\b/i.test(row.program.name) || row.category === "aggregation") return "consensus";
    return "misc";
  }

  function categoryRows() {
    return measurements.filter((row) => selectedCategory === "all" || categoryOf(row) === selectedCategory);
  }

  function populateFilters() {
    const sorted = categoryRows().sort(compareRows);
    populate(programFilter, new Map(sorted.map((row) => [row.program.name, row.program.name])), "All programs");
    populate(machineFilter, [...new Map(sorted.map((row) => [row.machine.id, text(row.machine.name, row.machine.id)]))].sort((a, b) => a[1].localeCompare(b[1])), "All machines & devices");
    const threads = [...new Map(sorted.map((row) => [threadKey(row), threadLabel(row)]))];
    threads.sort((a, b) => a[1].localeCompare(b[1], "en", { numeric: true }));
    populate(threadFilter, threads, "All thread configurations");
  }

  function resetFilters() {
    programFilter.value = "";
    machineFilter.value = "";
    threadFilter.value = "";
    sortOrder.value = "program";
    render();
  }

  function details(label, child) {
    const node = element("details");
    node.append(element("summary", "", label), child);
    return node;
  }

  function cell(label) {
    const node = element("td");
    const mobileLabel = element("span", "cell-label", label);
    mobileLabel.setAttribute("aria-hidden", "true");
    node.append(mobileLabel);
    return node;
  }

  function hardwareDetails(machine) {
    const list = element("dl", "hardware");
    const memory = typeof machine.memory_bytes === "number" && machine.memory_bytes > 0
      ? `${numberFormat.format(machine.memory_bytes / 1024 ** 3)} GiB`
      : "Not recorded";
    const fields = [
      ["CPU / SoC", text(machine.cpu)],
      ["Architecture", text(machine.arch)],
      ["Operating system", text(machine.os)],
      ["Logical CPUs", Number.isInteger(machine.logical_cpus) && machine.logical_cpus > 0 ? String(machine.logical_cpus) : "Not recorded"],
      ["Memory", memory],
    ];
    for (const [label, value] of fields) list.append(element("dt", "", label), element("dd", "", value));
    return details("Hardware details", list);
  }

  function repositoryUrl(repository) {
    const value = text(repository, "");
    if (/^[\w.-]+\/[\w.-]+$/.test(value)) return `https://github.com/${value}`;
    return safeUrl(value);
  }

  function provenance(row) {
    const node = cell("Provenance");
    const source = row.source || {};
    const label = text(source.label, source.kind === "pull_request" ? "Pull-request result" : source.kind === "branch" ? "Branch result" : "Source result");
    const labelClass = source.kind === "pull_request" ? "provenance-label pull-request" : "provenance-label";
    node.append(element("span", labelClass, label));
    node.append(dateNode(source.measured_at, "measured-at", "Measurement date not recorded"));
    const links = element("div", "provenance-links");
    const repository = repositoryUrl(source.repository);
    const commit = text(source.commit, "");
    const commitUrl = repository && /^[a-f0-9]{7,64}$/i.test(commit)
      ? `${repository.replace(/\/$/, "")}/commit/${commit}` : null;
    const revision = link(commit ? commit.slice(0, 8) : "Revision not recorded", commitUrl, "revision");
    if (commit) {
      revision.title = commit;
      revision.setAttribute("aria-label", `Source revision ${commit}`);
    }
    node.append(revision);
    if (safeUrl(source.run_url)) links.append(link("Benchmark run ↗", source.run_url));
    const metadata = element("div", "source-details");
    metadata.append(element("span", "provenance-source", text(source.repository, "Repository not recorded")));
    metadata.append(element("span", "provenance-source", `Branch: ${text(source.branch)}`));
    const verification = row.verification;
    if (Number.isInteger(verification?.verified_proofs) && Number.isInteger(verification?.total_proofs)
      && verification.verified_proofs >= 0 && verification.total_proofs > 0) {
      metadata.append(element("span", "verification", `${verification.verified_proofs} / ${verification.total_proofs} proofs verified`));
    }
    metadata.prepend(links);
    node.append(details("Source & verification", metadata));
    return node;
  }

  function resultRow(row) {
    const node = element("tr");
    const program = cell("Program / workload");
    program.append(element("h3", "row-title", row.program.name));
    program.append(element("p", "workload", row.workload));
    program.append(link(safeUrl(row.program.source_url) ? "Program source ↗" : "Program source not recorded", row.program.source_url, "source-link"));
    if (row.category === "aggregation") program.append(element("span", "category", "Aggregation workload"));
    if (selectedCategory === "all") {
      const category = categoryOf(row);
      program.append(element("span", `use-case ${category}`, categories[category].name));
    }

    const machine = cell("Machine / device");
    machine.append(element("p", "row-title", text(row.machine.name, row.machine.id)));
    if (text(row.machine.arch, "")) machine.append(element("p", "machine-platform", row.machine.arch));
    machine.append(hardwareDetails(row.machine));

    const threads = cell("Threads");
    threads.append(element("span", "chip", threadLabel(row)));

    const runtime = cell("Median runtime");
    const median = element("div", "timing", seconds(row.median_seconds));
    median.append(element("span", "timing-unit", " s"));
    median.setAttribute("aria-label", `Median ${row.median_seconds} seconds`);
    const range = element("span", "range", `${seconds(row.min_seconds)} to ${seconds(row.max_seconds)} s`);
    range.append(element("span", "range-label", "Observed min to max"));
    const samples = element("ol", "samples");
    for (const sample of row.samples_seconds) samples.append(element("li", "", `${sample} s`));
    runtime.append(median, range, details(`${row.samples_seconds.length} ${row.samples_seconds.length === 1 ? "sample" : "samples"}`, samples));
    node.append(program, machine, threads, runtime, provenance(row));
    return node;
  }

  function compareRows(left, right) {
    return left.program.name.localeCompare(right.program.name)
      || left.workload.localeCompare(right.workload, "en", { numeric: true })
      || text(left.machine.name, left.machine.id).localeCompare(text(right.machine.name, right.machine.id))
      || (left.threads?.count ?? Infinity) - (right.threads?.count ?? Infinity)
      || threadLabel(left).localeCompare(threadLabel(right))
      || left.id.localeCompare(right.id);
  }

  function render() {
    const available = categoryRows();
    const categoryOrder = Object.keys(categories);
    const shown = available.filter((row) =>
      (!programFilter.value || row.program.name === programFilter.value)
      && (!machineFilter.value || row.machine.id === machineFilter.value)
      && (!threadFilter.value || threadKey(row) === threadFilter.value));
    shown.sort((left, right) => {
      if (sortOrder.value === "recent") {
        const difference = (timestamp(right.source?.measured_at) ?? -Infinity) - (timestamp(left.source?.measured_at) ?? -Infinity);
        if (difference && !Number.isNaN(difference)) return difference;
      }
      if (selectedCategory === "all" && sortOrder.value === "program") {
        const difference = categoryOrder.indexOf(categoryOf(left)) - categoryOrder.indexOf(categoryOf(right));
        if (difference) return difference;
      }
      return compareRows(left, right);
    });
    const fragment = document.createDocumentFragment();
    for (const row of shown) fragment.append(resultRow(row));
    byId("result-rows").replaceChildren(fragment);
    byId("table-container").hidden = shown.length === 0;
    byId("empty-state").hidden = shown.length !== 0;
    const emptyDataset = measurements.length === 0;
    byId("empty-title").textContent = available.length === 0 ? "No published measurements yet." : "No matching measurements.";
    byId("empty-description").textContent = emptyDataset
      ? "This dataset does not contain any program or aggregation measurements."
      : available.length === 0
        ? `The current dataset has no measurements for ${categories[selectedCategory].name}.`
        : "Try a different program, machine or thread configuration.";
    byId("clear-filters").hidden = available.length === 0;
    byId("results-title").textContent = categories[selectedCategory].name;
    byId("category-description").textContent = categories[selectedCategory].description;
    byId("status").textContent = `${shown.length} of ${available.length} configurations · ${new Set(shown.map((row) => row.program.name)).size} programs · ${new Set(shown.map((row) => row.machine.id)).size} machines & devices`;
    for (const button of categoryBrowser.querySelectorAll("[data-category]")) {
      button.setAttribute("aria-pressed", String(button.dataset.category === selectedCategory));
    }
  }

  function populate(select, values, allLabel) {
    select.replaceChildren(element("option", "", allLabel));
    select.firstElementChild.value = "";
    for (const [value, label] of values) {
      const option = element("option", "", label);
      option.value = value;
      select.append(option);
    }
  }

  function updateCategoryCounts() {
    for (const category of Object.keys(categories)) {
      const count = category === "all" ? measurements.length : measurements.filter((row) => categoryOf(row) === category).length;
      byId(`${category}-count`).textContent = count;
      byId(`${category}-count`).setAttribute("aria-label", `${count} configurations`);
    }
  }

  function parseDataset(dataset) {
    if (!dataset || dataset.schema_version !== 1 || !Array.isArray(dataset.results)) throw new Error("Unsupported results format");
    const rows = dataset.results.filter((row) => row && ["program", "aggregation"].includes(row.category));
    const validTime = (value) => typeof value === "number" && Number.isFinite(value) && value >= 0;
    for (const row of rows) {
      if (!text(row.id, "") || !text(row.program?.name, "") || !text(row.workload, "") || !text(row.machine?.id, "")
        || ![row.median_seconds, row.min_seconds, row.max_seconds].every(validTime)
        || row.min_seconds > row.median_seconds || row.median_seconds > row.max_seconds
        || !Array.isArray(row.samples_seconds) || !row.samples_seconds.length || !row.samples_seconds.every(validTime)) {
        throw new Error("Invalid measurement record");
      }
    }
    return rows;
  }

  async function load() {
    results.setAttribute("aria-busy", "true");
    byId("error-state").hidden = true;
    byId("empty-state").hidden = true;
    byId("table-container").hidden = true;
    categoryBrowser.hidden = true;
    filters.hidden = true;
    byId("status").textContent = "Loading benchmark measurements…";
    try {
      const response = await fetch("./latest.json", { cache: "no-cache" });
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      const dataset = await response.json();
      measurements = parseDataset(dataset);
      populateFilters();
      sortOrder.value = "program";
      updateCategoryCounts();
      filters.hidden = measurements.length === 0;
      categoryBrowser.hidden = measurements.length === 0;
      render();
    } catch {
      measurements = [];
      byId("result-rows").replaceChildren();
      byId("status").textContent = "Measurements unavailable. No cached or example results are being shown.";
      byId("error-state").hidden = false;
    } finally {
      results.setAttribute("aria-busy", "false");
    }
  }

  categoryBrowser.addEventListener("click", (event) => {
    const button = event.target.closest("[data-category]");
    if (!button || button.dataset.category === selectedCategory) return;
    selectedCategory = button.dataset.category;
    populateFilters();
    render();
  });
  filters.addEventListener("submit", (event) => event.preventDefault());
  filters.addEventListener("change", render);
  filters.addEventListener("reset", (event) => {
    event.preventDefault();
    resetFilters();
  });
  byId("clear-filters").addEventListener("click", resetFilters);
  byId("retry").addEventListener("click", load);
  load();
})();
